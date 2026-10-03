/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
module

public import LeanPool.MovingSofa.GerverSofa.KernelOnly.Core.Bundle005
/-!
# Gerver sofa: related certificate and semantic modules

* `GerverSofa.KernelOnly.PartE.Certificates.Batch020`.
-/

public section

noncomputable section

namespace GerverSofa.PartE.CertificateCellsea1d7ddac9

/-- Subcell `0000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0000 : AngleCell :=
  childLL (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `0001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell0001 : AngleCell :=
  childLH (childLL (childLL (childLL e24ThetaAboveRoot)))

/-- Subcell `00003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell0000)))

/-- Subcell `00012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell0001)))

/-- Subcell `00012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `00012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell00012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell0001)))

/-- Subcell `000033102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00003310)))

/-- Subcell `000033102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00003310)))

/-- Subcell `000033103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00003310)))

/-- Subcell `000033103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00003310)))

/-- Subcell `000033112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00003311)))

/-- Subcell `000033112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00003311)))

/-- Subcell `000033113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00003311)))

/-- Subcell `000033113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000033113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000033113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00003311)))

/-- Subcell `000122002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012200)))

/-- Subcell `000122002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012200)))

/-- Subcell `000122003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012200)))

/-- Subcell `000122003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012200)))

/-- Subcell `000122012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012201)))

/-- Subcell `000122012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012201)))

/-- Subcell `000122013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012201)))

/-- Subcell `000122013300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122013313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122013313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012201)))

/-- Subcell `000122102000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012210)))

/-- Subcell `000122102300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122102313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122102313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012210)))

/-- Subcell `000122103000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012210)))

/-- Subcell `000122103300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122103313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122103313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012210)))

/-- Subcell `000122112000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012211)))

/-- Subcell `000122112300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122112313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122112313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012211)))

/-- Subcell `000122113000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012211)))

/-- Subcell `000122113300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000122113313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000122113313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012211)))

/-- Subcell `000123002000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012300)))

/-- Subcell `000123002300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123002313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123002313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012300)))

/-- Subcell `000123003000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003100 : AngleCell :=
  childLL (childLL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003101 : AngleCell :=
  childLH (childLL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003102 : AngleCell :=
  childHL (childLL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003103 : AngleCell :=
  childHH (childLL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003110 : AngleCell :=
  childLL (childLH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003111 : AngleCell :=
  childLH (childLH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003112 : AngleCell :=
  childHL (childLH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003113 : AngleCell :=
  childHH (childLH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003120 : AngleCell :=
  childLL (childHL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003121 : AngleCell :=
  childLH (childHL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003122 : AngleCell :=
  childHL (childHL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003123 : AngleCell :=
  childHH (childHL (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003130 : AngleCell :=
  childLL (childHH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003131 : AngleCell :=
  childLH (childHH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003132 : AngleCell :=
  childHL (childHH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003133 : AngleCell :=
  childHH (childHH (childLH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003200 : AngleCell :=
  childLL (childLL (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003201 : AngleCell :=
  childLH (childLL (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003202 : AngleCell :=
  childHL (childLL (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003203 : AngleCell :=
  childHH (childLL (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003210 : AngleCell :=
  childLL (childLH (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003211 : AngleCell :=
  childLH (childLH (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003212 : AngleCell :=
  childHL (childLH (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003213 : AngleCell :=
  childHH (childLH (childHL (childHH thetaAboveCell00012300)))

/-- Subcell `000123003300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003300 : AngleCell :=
  childLL (childLL (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003301 : AngleCell :=
  childLH (childLL (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003302 : AngleCell :=
  childHL (childLL (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003303 : AngleCell :=
  childHH (childLL (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003310 : AngleCell :=
  childLL (childLH (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003311 : AngleCell :=
  childLH (childLH (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003312 : AngleCell :=
  childHL (childLH (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123003313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123003313 : AngleCell :=
  childHH (childLH (childHH (childHH thetaAboveCell00012300)))

/-- Subcell `000123012000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012000 : AngleCell :=
  childLL (childLL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012001 : AngleCell :=
  childLH (childLL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012002 : AngleCell :=
  childHL (childLL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012003 : AngleCell :=
  childHH (childLL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012010 : AngleCell :=
  childLL (childLH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012011 : AngleCell :=
  childLH (childLH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012012 : AngleCell :=
  childHL (childLH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012013 : AngleCell :=
  childHH (childLH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012020 : AngleCell :=
  childLL (childHL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012021 : AngleCell :=
  childLH (childHL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012022 : AngleCell :=
  childHL (childHL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012023 : AngleCell :=
  childHH (childHL (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012030 : AngleCell :=
  childLL (childHH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012031 : AngleCell :=
  childLH (childHH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012032 : AngleCell :=
  childHL (childHH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012033 : AngleCell :=
  childHH (childHH (childLL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012100` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012100 : AngleCell :=
  childLL (childLL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012101` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012101 : AngleCell :=
  childLH (childLL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012102` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012102 : AngleCell :=
  childHL (childLL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012103` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012103 : AngleCell :=
  childHH (childLL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012110` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012110 : AngleCell :=
  childLL (childLH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012111` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012111 : AngleCell :=
  childLH (childLH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012112` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012112 : AngleCell :=
  childHL (childLH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012113` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012113 : AngleCell :=
  childHH (childLH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012120` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012120 : AngleCell :=
  childLL (childHL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012121` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012121 : AngleCell :=
  childLH (childHL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012122` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012122 : AngleCell :=
  childHL (childHL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012123` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012123 : AngleCell :=
  childHH (childHL (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012130` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012130 : AngleCell :=
  childLL (childHH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012131` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012131 : AngleCell :=
  childLH (childHH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012132` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012132 : AngleCell :=
  childHL (childHH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012133` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012133 : AngleCell :=
  childHH (childHH (childLH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012200` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012200 : AngleCell :=
  childLL (childLL (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012201` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012201 : AngleCell :=
  childLH (childLL (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012202` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012202 : AngleCell :=
  childHL (childLL (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012203` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012203 : AngleCell :=
  childHH (childLL (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012210` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012210 : AngleCell :=
  childLL (childLH (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012211` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012211 : AngleCell :=
  childLH (childLH (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012212` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012212 : AngleCell :=
  childHL (childLH (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012213` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012213 : AngleCell :=
  childHH (childLH (childHL (childHL thetaAboveCell00012301)))

/-- Subcell `000123012300` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012300 : AngleCell :=
  childLL (childLL (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012301` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012301 : AngleCell :=
  childLH (childLL (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012302` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012302 : AngleCell :=
  childHL (childLL (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012303` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012303 : AngleCell :=
  childHH (childLL (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012310` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012310 : AngleCell :=
  childLL (childLH (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012311` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012311 : AngleCell :=
  childLH (childLH (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012312` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012312 : AngleCell :=
  childHL (childLH (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123012313` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123012313 : AngleCell :=
  childHH (childLH (childHH (childHL thetaAboveCell00012301)))

/-- Subcell `000123013000` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013000 : AngleCell :=
  childLL (childLL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013001` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013001 : AngleCell :=
  childLH (childLL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013002` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013002 : AngleCell :=
  childHL (childLL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013003` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013003 : AngleCell :=
  childHH (childLL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013010` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013010 : AngleCell :=
  childLL (childLH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013011` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013011 : AngleCell :=
  childLH (childLH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013012` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013012 : AngleCell :=
  childHL (childLH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013013` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013013 : AngleCell :=
  childHH (childLH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013020` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013020 : AngleCell :=
  childLL (childHL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013021` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013021 : AngleCell :=
  childLH (childHL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013022` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013022 : AngleCell :=
  childHL (childHL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013023` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013023 : AngleCell :=
  childHH (childHL (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013030` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013030 : AngleCell :=
  childLL (childHH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013031` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013031 : AngleCell :=
  childLH (childHH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013032` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013032 : AngleCell :=
  childHL (childHH (childLL (childHH thetaAboveCell00012301)))

/-- Subcell `000123013033` of the theta-above root; digits 0–3 mean LL, LH, HL, HH. -/
abbrev thetaAboveCell000123013033 : AngleCell :=
  childHH (childHH (childLL (childHH thetaAboveCell00012301)))

end GerverSofa.PartE.CertificateCellsea1d7ddac9

section

/-
Copyright (c) 2026 Dawid Trela. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dawid Trela
-/
/-!
# Gerver sofa dependency batch

* `KernelOnly.PartE.E24KC6ProofBatch32fd0d2bad1c3ab1`.
-/

public section

noncomputable section

section

/-! E24KC6 explicit proof-producing certificate batch. -/

public section

noncomputable section

namespace GerverSofa
namespace PartE

namespace CertificateCellsea1d7ddac9

-- Base-four digits encode LL, LH, HL, HH subdivisions of the named root.

end CertificateCellsea1d7ddac9

open CertificateCellsea1d7ddac9
theorem cover_subtree_0099e6c88888 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102100 h)
    (by
      have h : (thetaAboveCell000033102101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102102
        (by
          have h : ((childLL thetaAboveCell000033102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102102) h)
        (by
          have h : ((childLH thetaAboveCell000033102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102102) h)
        (by
          have h : ((childHL thetaAboveCell000033102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102102) h)
        (by
          have h : ((childHH thetaAboveCell000033102102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102103
        (by
          have h : ((childLL thetaAboveCell000033102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102103) h)
        (by
          have h : ((childLH thetaAboveCell000033102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102103) h)
        (by
          have h : ((childHL thetaAboveCell000033102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102103) h)
        (by
          have h : ((childHH thetaAboveCell000033102103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102103) h))

theorem cover_subtree_ba641df32bfd :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033102110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102110 h)
    (by
      have h : (thetaAboveCell000033102111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102112
        (by
          have h : ((childLL thetaAboveCell000033102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102112) h)
        (by
          have h : ((childLH thetaAboveCell000033102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102112) h)
        (by
          have h : ((childHL thetaAboveCell000033102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102112) h)
        (by
          have h : ((childHH thetaAboveCell000033102112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102113
        (by
          have h : ((childLL thetaAboveCell000033102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102113) h)
        (by
          have h : ((childLH thetaAboveCell000033102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102113) h)
        (by
          have h : ((childHL thetaAboveCell000033102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102113) h)
        (by
          have h : ((childHH thetaAboveCell000033102113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102113) h))

theorem cover_subtree_7ba93df0d4c7 :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102120
        (by
          have h : ((childLL thetaAboveCell000033102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102120) h)
        (by
          have h : ((childLH thetaAboveCell000033102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102120) h)
        (by
          have h : ((childHL thetaAboveCell000033102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102120) h)
        (by
          have h : ((childHH thetaAboveCell000033102120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102121
        (by
          have h : ((childLL thetaAboveCell000033102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102121) h)
        (by
          have h : ((childLH thetaAboveCell000033102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102121) h)
        (by
          have h : ((childHL thetaAboveCell000033102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102121) h)
        (by
          have h : ((childHH thetaAboveCell000033102121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102122
        (by
          have h : ((childLL thetaAboveCell000033102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102122) h)
        (by
          have h : ((childLH thetaAboveCell000033102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102122) h)
        (by
          have h : ((childHL thetaAboveCell000033102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102122) h)
        (by
          have h : ((childHH thetaAboveCell000033102122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102123
        (by
          have h : ((childLL thetaAboveCell000033102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102123) h)
        (by
          have h : ((childLH thetaAboveCell000033102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102123) h)
        (by
          have h : ((childHL thetaAboveCell000033102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102123) h)
        (by
          have h : ((childHH thetaAboveCell000033102123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102123) h))

theorem cover_subtree_65f8fb6981b4 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102130
        (by
          have h : ((childLL thetaAboveCell000033102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102130) h)
        (by
          have h : ((childLH thetaAboveCell000033102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102130) h)
        (by
          have h : ((childHL thetaAboveCell000033102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102130) h)
        (by
          have h : ((childHH thetaAboveCell000033102130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102131
        (by
          have h : ((childLL thetaAboveCell000033102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102131) h)
        (by
          have h : ((childLH thetaAboveCell000033102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102131) h)
        (by
          have h : ((childHL thetaAboveCell000033102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102131) h)
        (by
          have h : ((childHH thetaAboveCell000033102131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102132
        (by
          have h : ((childLL thetaAboveCell000033102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102132) h)
        (by
          have h : ((childLH thetaAboveCell000033102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102132) h)
        (by
          have h : ((childHL thetaAboveCell000033102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102132) h)
        (by
          have h : ((childHH thetaAboveCell000033102132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033102133
        (by
          have h : ((childLL thetaAboveCell000033102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033102133) h)
        (by
          have h : ((childLH thetaAboveCell000033102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033102133) h)
        (by
          have h : ((childHL thetaAboveCell000033102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033102133) h)
        (by
          have h : ((childHH thetaAboveCell000033102133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033102133) h))

theorem e24KC2ThetaAboveLeaf0000331021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003310))
    cover_subtree_0099e6c88888
    cover_subtree_ba641df32bfd
    cover_subtree_7ba93df0d4c7
    cover_subtree_65f8fb6981b4
theorem e24KC2ThetaAboveLeaf0000331022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102200 h)
        (by
          have h : (thetaAboveCell000033102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102201 h)
        (by
          have h : (thetaAboveCell000033102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102202 h)
        (by
          have h : (thetaAboveCell000033102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102210 h)
        (by
          have h : (thetaAboveCell000033102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102211 h)
        (by
          have h : (thetaAboveCell000033102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102212 h)
        (by
          have h : (thetaAboveCell000033102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102300 h)
        (by
          have h : (thetaAboveCell000033102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102301 h)
        (by
          have h : (thetaAboveCell000033102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102302 h)
        (by
          have h : (thetaAboveCell000033102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102310 h)
        (by
          have h : (thetaAboveCell000033102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102311 h)
        (by
          have h : (thetaAboveCell000033102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102312 h)
        (by
          have h : (thetaAboveCell000033102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003310))) h)
theorem cover_subtree_3709c9a249b6 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033103000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103000 h)
    (by
      have h : (thetaAboveCell000033103001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103002
        (by
          have h : ((childLL thetaAboveCell000033103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103002) h)
        (by
          have h : ((childLH thetaAboveCell000033103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103002) h)
        (by
          have h : ((childHL thetaAboveCell000033103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103002) h)
        (by
          have h : ((childHH thetaAboveCell000033103002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103003
        (by
          have h : ((childLL thetaAboveCell000033103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103003) h)
        (by
          have h : ((childLH thetaAboveCell000033103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103003) h)
        (by
          have h : ((childHL thetaAboveCell000033103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103003) h)
        (by
          have h : ((childHH thetaAboveCell000033103003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103003) h))

theorem cover_subtree_2b5889a2610f :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033103010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103010 h)
    (by
      have h : (thetaAboveCell000033103011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103012
        (by
          have h : ((childLL thetaAboveCell000033103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103012) h)
        (by
          have h : ((childLH thetaAboveCell000033103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103012) h)
        (by
          have h : ((childHL thetaAboveCell000033103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103012) h)
        (by
          have h : ((childHH thetaAboveCell000033103012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103013
        (by
          have h : ((childLL thetaAboveCell000033103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103013) h)
        (by
          have h : ((childLH thetaAboveCell000033103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103013) h)
        (by
          have h : ((childHL thetaAboveCell000033103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103013) h)
        (by
          have h : ((childHH thetaAboveCell000033103013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103013) h))

theorem cover_subtree_81afd77398fe :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103020
        (by
          have h : ((childLL thetaAboveCell000033103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103020) h)
        (by
          have h : ((childLH thetaAboveCell000033103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103020) h)
        (by
          have h : ((childHL thetaAboveCell000033103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103020) h)
        (by
          have h : ((childHH thetaAboveCell000033103020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103021
        (by
          have h : ((childLL thetaAboveCell000033103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103021) h)
        (by
          have h : ((childLH thetaAboveCell000033103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103021) h)
        (by
          have h : ((childHL thetaAboveCell000033103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103021) h)
        (by
          have h : ((childHH thetaAboveCell000033103021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103022
        (by
          have h : ((childLL thetaAboveCell000033103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103022) h)
        (by
          have h : ((childLH thetaAboveCell000033103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103022) h)
        (by
          have h : ((childHL thetaAboveCell000033103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103022) h)
        (by
          have h : ((childHH thetaAboveCell000033103022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103023
        (by
          have h : ((childLL thetaAboveCell000033103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103023) h)
        (by
          have h : ((childLH thetaAboveCell000033103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103023) h)
        (by
          have h : ((childHL thetaAboveCell000033103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103023) h)
        (by
          have h : ((childHH thetaAboveCell000033103023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103023) h))

theorem cover_subtree_56217b7b19f0 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103030
        (by
          have h : ((childLL thetaAboveCell000033103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103030) h)
        (by
          have h : ((childLH thetaAboveCell000033103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103030) h)
        (by
          have h : ((childHL thetaAboveCell000033103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103030) h)
        (by
          have h : ((childHH thetaAboveCell000033103030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103031
        (by
          have h : ((childLL thetaAboveCell000033103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103031) h)
        (by
          have h : ((childLH thetaAboveCell000033103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103031) h)
        (by
          have h : ((childHL thetaAboveCell000033103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103031) h)
        (by
          have h : ((childHH thetaAboveCell000033103031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103032
        (by
          have h : ((childLL thetaAboveCell000033103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103032) h)
        (by
          have h : ((childLH thetaAboveCell000033103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103032) h)
        (by
          have h : ((childHL thetaAboveCell000033103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103032) h)
        (by
          have h : ((childHH thetaAboveCell000033103032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103033
        (by
          have h : ((childLL thetaAboveCell000033103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103033) h)
        (by
          have h : ((childLH thetaAboveCell000033103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103033) h)
        (by
          have h : ((childHL thetaAboveCell000033103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103033) h)
        (by
          have h : ((childHH thetaAboveCell000033103033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103033) h))

theorem e24KC2ThetaAboveLeaf0000331030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003310))
    cover_subtree_3709c9a249b6
    cover_subtree_2b5889a2610f
    cover_subtree_81afd77398fe
    cover_subtree_56217b7b19f0
theorem cover_subtree_126d0c7909f0 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033103100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103100 h)
    (by
      have h : (thetaAboveCell000033103101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103102
        (by
          have h : ((childLL thetaAboveCell000033103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103102) h)
        (by
          have h : ((childLH thetaAboveCell000033103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103102) h)
        (by
          have h : ((childHL thetaAboveCell000033103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103102) h)
        (by
          have h : ((childHH thetaAboveCell000033103102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103103
        (by
          have h : ((childLL thetaAboveCell000033103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103103) h)
        (by
          have h : ((childLH thetaAboveCell000033103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103103) h)
        (by
          have h : ((childHL thetaAboveCell000033103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103103) h)
        (by
          have h : ((childHH thetaAboveCell000033103103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103103) h))

theorem cover_subtree_978b69a1c1bd :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003310)))
    (by
      have h : (thetaAboveCell000033103110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103110 h)
    (by
      have h : (thetaAboveCell000033103111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103112
        (by
          have h : ((childLL thetaAboveCell000033103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103112) h)
        (by
          have h : ((childLH thetaAboveCell000033103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103112) h)
        (by
          have h : ((childHL thetaAboveCell000033103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103112) h)
        (by
          have h : ((childHH thetaAboveCell000033103112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103113
        (by
          have h : ((childLL thetaAboveCell000033103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103113) h)
        (by
          have h : ((childLH thetaAboveCell000033103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103113) h)
        (by
          have h : ((childHL thetaAboveCell000033103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103113) h)
        (by
          have h : ((childHH thetaAboveCell000033103113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103113) h))

theorem cover_subtree_6f4368c59bdb :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103120
        (by
          have h : ((childLL thetaAboveCell000033103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103120) h)
        (by
          have h : ((childLH thetaAboveCell000033103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103120) h)
        (by
          have h : ((childHL thetaAboveCell000033103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103120) h)
        (by
          have h : ((childHH thetaAboveCell000033103120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103121
        (by
          have h : ((childLL thetaAboveCell000033103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103121) h)
        (by
          have h : ((childLH thetaAboveCell000033103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103121) h)
        (by
          have h : ((childHL thetaAboveCell000033103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103121) h)
        (by
          have h : ((childHH thetaAboveCell000033103121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103122
        (by
          have h : ((childLL thetaAboveCell000033103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103122) h)
        (by
          have h : ((childLH thetaAboveCell000033103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103122) h)
        (by
          have h : ((childHL thetaAboveCell000033103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103122) h)
        (by
          have h : ((childHH thetaAboveCell000033103122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103123
        (by
          have h : ((childLL thetaAboveCell000033103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103123) h)
        (by
          have h : ((childLH thetaAboveCell000033103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103123) h)
        (by
          have h : ((childHL thetaAboveCell000033103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103123) h)
        (by
          have h : ((childHH thetaAboveCell000033103123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103123) h))

theorem cover_subtree_12a65271b941 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003310))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003310)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103130
        (by
          have h : ((childLL thetaAboveCell000033103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103130) h)
        (by
          have h : ((childLH thetaAboveCell000033103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103130) h)
        (by
          have h : ((childHL thetaAboveCell000033103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103130) h)
        (by
          have h : ((childHH thetaAboveCell000033103130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103131
        (by
          have h : ((childLL thetaAboveCell000033103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103131) h)
        (by
          have h : ((childLH thetaAboveCell000033103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103131) h)
        (by
          have h : ((childHL thetaAboveCell000033103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103131) h)
        (by
          have h : ((childHH thetaAboveCell000033103131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103131) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103132
        (by
          have h : ((childLL thetaAboveCell000033103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103132) h)
        (by
          have h : ((childLH thetaAboveCell000033103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103132) h)
        (by
          have h : ((childHL thetaAboveCell000033103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103132) h)
        (by
          have h : ((childHH thetaAboveCell000033103132)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103132) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033103133
        (by
          have h : ((childLL thetaAboveCell000033103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033103133) h)
        (by
          have h : ((childLH thetaAboveCell000033103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033103133) h)
        (by
          have h : ((childHL thetaAboveCell000033103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033103133) h)
        (by
          have h : ((childHH thetaAboveCell000033103133)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033103133) h))

theorem e24KC2ThetaAboveLeaf0000331031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003310))
    cover_subtree_126d0c7909f0
    cover_subtree_978b69a1c1bd
    cover_subtree_6f4368c59bdb
    cover_subtree_12a65271b941
theorem e24KC2ThetaAboveLeaf0000331032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103200 h)
        (by
          have h : (thetaAboveCell000033103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103201 h)
        (by
          have h : (thetaAboveCell000033103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103202 h)
        (by
          have h : (thetaAboveCell000033103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103210 h)
        (by
          have h : (thetaAboveCell000033103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103211 h)
        (by
          have h : (thetaAboveCell000033103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103212 h)
        (by
          have h : (thetaAboveCell000033103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003310)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003310))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103300 h)
        (by
          have h : (thetaAboveCell000033103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103301 h)
        (by
          have h : (thetaAboveCell000033103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103302 h)
        (by
          have h : (thetaAboveCell000033103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00003310)))
        (by
          have h : (thetaAboveCell000033103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103310 h)
        (by
          have h : (thetaAboveCell000033103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103311 h)
        (by
          have h : (thetaAboveCell000033103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103312 h)
        (by
          have h : (thetaAboveCell000033103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003310))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003310)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003310))) h)
theorem e24KC2ThetaAboveLeaf0000331102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00003311))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0000331103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00003311))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0000331112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00003311))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0000331113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00003311))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00003311))) h)
theorem cover_subtree_40b30098358c :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033112000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112000 h)
    (by
      have h : (thetaAboveCell000033112001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112002
        (by
          have h : ((childLL thetaAboveCell000033112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112002) h)
        (by
          have h : ((childLH thetaAboveCell000033112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112002) h)
        (by
          have h : ((childHL thetaAboveCell000033112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112002) h)
        (by
          have h : ((childHH thetaAboveCell000033112002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112003
        (by
          have h : ((childLL thetaAboveCell000033112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112003) h)
        (by
          have h : ((childLH thetaAboveCell000033112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112003) h)
        (by
          have h : ((childHL thetaAboveCell000033112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112003) h)
        (by
          have h : ((childHH thetaAboveCell000033112003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112003) h))

theorem cover_subtree_0f9e0e377596 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033112010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112010 h)
    (by
      have h : (thetaAboveCell000033112011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112012
        (by
          have h : ((childLL thetaAboveCell000033112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112012) h)
        (by
          have h : ((childLH thetaAboveCell000033112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112012) h)
        (by
          have h : ((childHL thetaAboveCell000033112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112012) h)
        (by
          have h : ((childHH thetaAboveCell000033112012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112013
        (by
          have h : ((childLL thetaAboveCell000033112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112013) h)
        (by
          have h : ((childLH thetaAboveCell000033112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112013) h)
        (by
          have h : ((childHL thetaAboveCell000033112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112013) h)
        (by
          have h : ((childHH thetaAboveCell000033112013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112013) h))

theorem cover_subtree_562ee101dc47 :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112020
        (by
          have h : ((childLL thetaAboveCell000033112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112020) h)
        (by
          have h : ((childLH thetaAboveCell000033112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112020) h)
        (by
          have h : ((childHL thetaAboveCell000033112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112020) h)
        (by
          have h : ((childHH thetaAboveCell000033112020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112021
        (by
          have h : ((childLL thetaAboveCell000033112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112021) h)
        (by
          have h : ((childLH thetaAboveCell000033112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112021) h)
        (by
          have h : ((childHL thetaAboveCell000033112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112021) h)
        (by
          have h : ((childHH thetaAboveCell000033112021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112021) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112022
        (by
          have h : ((childLL thetaAboveCell000033112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112022) h)
        (by
          have h : ((childLH thetaAboveCell000033112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112022) h)
        (by
          have h : ((childHL thetaAboveCell000033112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112022) h)
        (by
          have h : ((childHH thetaAboveCell000033112022)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112022) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112023
        (by
          have h : ((childLL thetaAboveCell000033112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112023) h)
        (by
          have h : ((childLH thetaAboveCell000033112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112023) h)
        (by
          have h : ((childHL thetaAboveCell000033112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112023) h)
        (by
          have h : ((childHH thetaAboveCell000033112023)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112023) h))

theorem cover_subtree_bc17552a24a4 :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112030
        (by
          have h : ((childLL thetaAboveCell000033112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112030) h)
        (by
          have h : ((childLH thetaAboveCell000033112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112030) h)
        (by
          have h : ((childHL thetaAboveCell000033112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112030) h)
        (by
          have h : ((childHH thetaAboveCell000033112030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112031
        (by
          have h : ((childLL thetaAboveCell000033112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112031) h)
        (by
          have h : ((childLH thetaAboveCell000033112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112031) h)
        (by
          have h : ((childHL thetaAboveCell000033112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112031) h)
        (by
          have h : ((childHH thetaAboveCell000033112031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112031) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112032
        (by
          have h : ((childLL thetaAboveCell000033112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112032) h)
        (by
          have h : ((childLH thetaAboveCell000033112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112032) h)
        (by
          have h : ((childHL thetaAboveCell000033112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112032) h)
        (by
          have h : ((childHH thetaAboveCell000033112032)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112032) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112033
        (by
          have h : ((childLL thetaAboveCell000033112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112033) h)
        (by
          have h : ((childLH thetaAboveCell000033112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112033) h)
        (by
          have h : ((childHL thetaAboveCell000033112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112033) h)
        (by
          have h : ((childHH thetaAboveCell000033112033)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112033) h))

theorem e24KC2ThetaAboveLeaf0000331120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00003311))
    cover_subtree_40b30098358c
    cover_subtree_0f9e0e377596
    cover_subtree_562ee101dc47
    cover_subtree_bc17552a24a4
theorem cover_subtree_260aee4b9fa3 :
    adaptiveCoverCheck 8 (childLL (childLH (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033112100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112100 h)
    (by
      have h : (thetaAboveCell000033112101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112102
        (by
          have h : ((childLL thetaAboveCell000033112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112102) h)
        (by
          have h : ((childLH thetaAboveCell000033112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112102) h)
        (by
          have h : ((childHL thetaAboveCell000033112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112102) h)
        (by
          have h : ((childHH thetaAboveCell000033112102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112103
        (by
          have h : ((childLL thetaAboveCell000033112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112103) h)
        (by
          have h : ((childLH thetaAboveCell000033112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112103) h)
        (by
          have h : ((childHL thetaAboveCell000033112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112103) h)
        (by
          have h : ((childHH thetaAboveCell000033112103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112103) h))

theorem cover_subtree_674fd6a8471c :
    adaptiveCoverCheck 8 (childLH (childLH (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033112110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112110 h)
    (by
      have h : (thetaAboveCell000033112111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112112
        (by
          have h : ((childLL thetaAboveCell000033112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112112) h)
        (by
          have h : ((childLH thetaAboveCell000033112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112112) h)
        (by
          have h : ((childHL thetaAboveCell000033112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112112) h)
        (by
          have h : ((childHH thetaAboveCell000033112112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112113
        (by
          have h : ((childLL thetaAboveCell000033112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112113) h)
        (by
          have h : ((childLH thetaAboveCell000033112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112113) h)
        (by
          have h : ((childHL thetaAboveCell000033112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112113) h)
        (by
          have h : ((childHH thetaAboveCell000033112113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112113) h))

theorem cover_subtree_38509f162ffa :
    adaptiveCoverCheck 8 (childHL (childLH (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112120
        (by
          have h : ((childLL thetaAboveCell000033112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112120) h)
        (by
          have h : ((childLH thetaAboveCell000033112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112120) h)
        (by
          have h : ((childHL thetaAboveCell000033112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112120) h)
        (by
          have h : ((childHH thetaAboveCell000033112120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112121
        (by
          have h : ((childLL thetaAboveCell000033112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112121) h)
        (by
          have h : ((childLH thetaAboveCell000033112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112121) h)
        (by
          have h : ((childHL thetaAboveCell000033112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112121) h)
        (by
          have h : ((childHH thetaAboveCell000033112121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112121) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112122
        (by
          have h : ((childLL thetaAboveCell000033112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112122) h)
        (by
          have h : ((childLH thetaAboveCell000033112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112122) h)
        (by
          have h : ((childHL thetaAboveCell000033112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112122) h)
        (by
          have h : ((childHH thetaAboveCell000033112122)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112122) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112123
        (by
          have h : ((childLL thetaAboveCell000033112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112123) h)
        (by
          have h : ((childLH thetaAboveCell000033112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112123) h)
        (by
          have h : ((childHL thetaAboveCell000033112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112123) h)
        (by
          have h : ((childHH thetaAboveCell000033112123)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112123) h))

theorem cover_subtree_2b615745aa63 :
    adaptiveCoverCheck 8 (childHH (childLH (childHL thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112130
        (by
          have h : ((childLL thetaAboveCell000033112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112130) h)
        (by
          have h : ((childLH thetaAboveCell000033112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112130) h)
        (by
          have h : ((childHL thetaAboveCell000033112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112130) h)
        (by
          have h : ((childHH thetaAboveCell000033112130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033112131
        (by
          have h : ((childLL thetaAboveCell000033112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033112131) h)
        (by
          have h : ((childLH thetaAboveCell000033112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033112131) h)
        (by
          have h : ((childHL thetaAboveCell000033112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033112131) h)
        (by
          have h : ((childHH thetaAboveCell000033112131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033112131) h))
    (by
      have h : (thetaAboveCell000033112132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112132 h)
    (by
      have h : (thetaAboveCell000033112133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112133 h)

theorem e24KC2ThetaAboveLeaf0000331121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00003311))
    cover_subtree_260aee4b9fa3
    cover_subtree_674fd6a8471c
    cover_subtree_38509f162ffa
    cover_subtree_2b615745aa63
theorem e24KC2ThetaAboveLeaf0000331122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00003311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112200 h)
        (by
          have h : (thetaAboveCell000033112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112201 h)
        (by
          have h : (thetaAboveCell000033112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112202 h)
        (by
          have h : (thetaAboveCell000033112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112210 h)
        (by
          have h : (thetaAboveCell000033112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112211 h)
        (by
          have h : (thetaAboveCell000033112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112212 h)
        (by
          have h : (thetaAboveCell000033112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0000331123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00003311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112300 h)
        (by
          have h : (thetaAboveCell000033112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112301 h)
        (by
          have h : (thetaAboveCell000033112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112302 h)
        (by
          have h : (thetaAboveCell000033112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112310 h)
        (by
          have h : (thetaAboveCell000033112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112311 h)
        (by
          have h : (thetaAboveCell000033112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112312 h)
        (by
          have h : (thetaAboveCell000033112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00003311))) h)
theorem cover_subtree_7b02d095f599 :
    adaptiveCoverCheck 8 (childLL (childLL (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033113000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113000 h)
    (by
      have h : (thetaAboveCell000033113001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113002
        (by
          have h : ((childLL thetaAboveCell000033113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113002) h)
        (by
          have h : ((childLH thetaAboveCell000033113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113002) h)
        (by
          have h : ((childHL thetaAboveCell000033113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113002) h)
        (by
          have h : ((childHH thetaAboveCell000033113002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113003
        (by
          have h : ((childLL thetaAboveCell000033113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113003) h)
        (by
          have h : ((childLH thetaAboveCell000033113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113003) h)
        (by
          have h : ((childHL thetaAboveCell000033113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113003) h)
        (by
          have h : ((childHH thetaAboveCell000033113003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113003) h))

theorem cover_subtree_27bc40bbefb0 :
    adaptiveCoverCheck 8 (childLH (childLL (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033113010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113010 h)
    (by
      have h : (thetaAboveCell000033113011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113012
        (by
          have h : ((childLL thetaAboveCell000033113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113012) h)
        (by
          have h : ((childLH thetaAboveCell000033113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113012) h)
        (by
          have h : ((childHL thetaAboveCell000033113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113012) h)
        (by
          have h : ((childHH thetaAboveCell000033113012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113013
        (by
          have h : ((childLL thetaAboveCell000033113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113013) h)
        (by
          have h : ((childLH thetaAboveCell000033113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113013) h)
        (by
          have h : ((childHL thetaAboveCell000033113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113013) h)
        (by
          have h : ((childHH thetaAboveCell000033113013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113013) h))

theorem cover_subtree_d6ec9d4db7c3 :
    adaptiveCoverCheck 8 (childHL (childLL (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113020
        (by
          have h : ((childLL thetaAboveCell000033113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113020) h)
        (by
          have h : ((childLH thetaAboveCell000033113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113020) h)
        (by
          have h : ((childHL thetaAboveCell000033113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113020) h)
        (by
          have h : ((childHH thetaAboveCell000033113020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113021
        (by
          have h : ((childLL thetaAboveCell000033113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113021) h)
        (by
          have h : ((childLH thetaAboveCell000033113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113021) h)
        (by
          have h : ((childHL thetaAboveCell000033113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113021) h)
        (by
          have h : ((childHH thetaAboveCell000033113021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113021) h))
    (by
      have h : (thetaAboveCell000033113022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113022 h)
    (by
      have h : (thetaAboveCell000033113023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113023 h)

theorem cover_subtree_c7a6802137f2 :
    adaptiveCoverCheck 8 (childHH (childLL (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113030
        (by
          have h : ((childLL thetaAboveCell000033113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113030) h)
        (by
          have h : ((childLH thetaAboveCell000033113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113030) h)
        (by
          have h : ((childHL thetaAboveCell000033113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113030) h)
        (by
          have h : ((childHH thetaAboveCell000033113030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113031
        (by
          have h : ((childLL thetaAboveCell000033113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113031) h)
        (by
          have h : ((childLH thetaAboveCell000033113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113031) h)
        (by
          have h : ((childHL thetaAboveCell000033113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113031) h)
        (by
          have h : ((childHH thetaAboveCell000033113031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113031) h))
    (by
      have h : (thetaAboveCell000033113032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113032 h)
    (by
      have h : (thetaAboveCell000033113033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113033 h)

theorem e24KC2ThetaAboveLeaf0000331130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00003311))
    cover_subtree_7b02d095f599
    cover_subtree_27bc40bbefb0
    cover_subtree_d6ec9d4db7c3
    cover_subtree_c7a6802137f2
theorem cover_subtree_525965b29b43 :
    adaptiveCoverCheck 8 (childLL (childLH (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033113100).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113100 h)
    (by
      have h : (thetaAboveCell000033113101).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113101 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113102
        (by
          have h : ((childLL thetaAboveCell000033113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113102) h)
        (by
          have h : ((childLH thetaAboveCell000033113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113102) h)
        (by
          have h : ((childHL thetaAboveCell000033113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113102) h)
        (by
          have h : ((childHH thetaAboveCell000033113102)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113102) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113103
        (by
          have h : ((childLL thetaAboveCell000033113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113103) h)
        (by
          have h : ((childLH thetaAboveCell000033113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113103) h)
        (by
          have h : ((childHL thetaAboveCell000033113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113103) h)
        (by
          have h : ((childHH thetaAboveCell000033113103)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113103) h))

theorem cover_subtree_426a701a7fc0 :
    adaptiveCoverCheck 8 (childLH (childLH (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH thetaAboveCell00003311)))
    (by
      have h : (thetaAboveCell000033113110).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113110 h)
    (by
      have h : (thetaAboveCell000033113111).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113111 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113112
        (by
          have h : ((childLL thetaAboveCell000033113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113112) h)
        (by
          have h : ((childLH thetaAboveCell000033113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113112) h)
        (by
          have h : ((childHL thetaAboveCell000033113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113112) h)
        (by
          have h : ((childHH thetaAboveCell000033113112)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113112) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113113
        (by
          have h : ((childLL thetaAboveCell000033113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113113) h)
        (by
          have h : ((childLH thetaAboveCell000033113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113113) h)
        (by
          have h : ((childHL thetaAboveCell000033113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113113) h)
        (by
          have h : ((childHH thetaAboveCell000033113113)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113113) h))

theorem cover_subtree_c43488da1c36 :
    adaptiveCoverCheck 8 (childHL (childLH (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113120
        (by
          have h : ((childLL thetaAboveCell000033113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113120) h)
        (by
          have h : ((childLH thetaAboveCell000033113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113120) h)
        (by
          have h : ((childHL thetaAboveCell000033113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113120) h)
        (by
          have h : ((childHH thetaAboveCell000033113120)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113120) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113121
        (by
          have h : ((childLL thetaAboveCell000033113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113121) h)
        (by
          have h : ((childLH thetaAboveCell000033113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113121) h)
        (by
          have h : ((childHL thetaAboveCell000033113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113121) h)
        (by
          have h : ((childHH thetaAboveCell000033113121)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113121) h))
    (by
      have h : (thetaAboveCell000033113122).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113122 h)
    (by
      have h : (thetaAboveCell000033113123).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113123 h)

theorem cover_subtree_f77c14a0f9b2 :
    adaptiveCoverCheck 8 (childHH (childLH (childHH thetaAboveCell00003311))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH thetaAboveCell00003311)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113130
        (by
          have h : ((childLL thetaAboveCell000033113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113130) h)
        (by
          have h : ((childLH thetaAboveCell000033113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113130) h)
        (by
          have h : ((childHL thetaAboveCell000033113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113130) h)
        (by
          have h : ((childHH thetaAboveCell000033113130)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113130) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000033113131
        (by
          have h : ((childLL thetaAboveCell000033113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000033113131) h)
        (by
          have h : ((childLH thetaAboveCell000033113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000033113131) h)
        (by
          have h : ((childHL thetaAboveCell000033113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000033113131) h)
        (by
          have h : ((childHH thetaAboveCell000033113131)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000033113131) h))
    (by
      have h : (thetaAboveCell000033113132).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113132 h)
    (by
      have h : (thetaAboveCell000033113133).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113133 h)

theorem e24KC2ThetaAboveLeaf0000331131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00003311))
    cover_subtree_525965b29b43
    cover_subtree_426a701a7fc0
    cover_subtree_c43488da1c36
    cover_subtree_f77c14a0f9b2
theorem e24KC2ThetaAboveLeaf0000331132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00003311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113200 h)
        (by
          have h : (thetaAboveCell000033113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113201 h)
        (by
          have h : (thetaAboveCell000033113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113202 h)
        (by
          have h : (thetaAboveCell000033113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113210 h)
        (by
          have h : (thetaAboveCell000033113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113211 h)
        (by
          have h : (thetaAboveCell000033113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113212 h)
        (by
          have h : (thetaAboveCell000033113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0000331133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00003311)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00003311))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113300 h)
        (by
          have h : (thetaAboveCell000033113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113301 h)
        (by
          have h : (thetaAboveCell000033113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113302 h)
        (by
          have h : (thetaAboveCell000033113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00003311)))
        (by
          have h : (thetaAboveCell000033113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113310 h)
        (by
          have h : (thetaAboveCell000033113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113311 h)
        (by
          have h : (thetaAboveCell000033113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113312 h)
        (by
          have h : (thetaAboveCell000033113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000033113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00003311))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00003311)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00003311))) h)
theorem e24KC2ThetaAboveLeaf0001220002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012200))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012200))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012200))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012200))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012200))) h)
theorem cover_subtree_bc394da66032 :
    adaptiveCoverCheck 8 (childLL (childLL (childHL thetaAboveCell00012200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL thetaAboveCell00012200)))
    (by
      have h : (thetaAboveCell000122002000).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002000 h)
    (by
      have h : (thetaAboveCell000122002001).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002001 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002002
        (by
          have h : ((childLL thetaAboveCell000122002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002002) h)
        (by
          have h : ((childLH thetaAboveCell000122002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002002) h)
        (by
          have h : ((childHL thetaAboveCell000122002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002002) h)
        (by
          have h : ((childHH thetaAboveCell000122002002)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002002) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002003
        (by
          have h : ((childLL thetaAboveCell000122002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002003) h)
        (by
          have h : ((childLH thetaAboveCell000122002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002003) h)
        (by
          have h : ((childHL thetaAboveCell000122002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002003) h)
        (by
          have h : ((childHH thetaAboveCell000122002003)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002003) h))

theorem cover_subtree_0f99148bdc12 :
    adaptiveCoverCheck 8 (childLH (childLL (childHL thetaAboveCell00012200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL thetaAboveCell00012200)))
    (by
      have h : (thetaAboveCell000122002010).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002010 h)
    (by
      have h : (thetaAboveCell000122002011).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002011 h)
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002012
        (by
          have h : ((childLL thetaAboveCell000122002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002012) h)
        (by
          have h : ((childLH thetaAboveCell000122002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002012) h)
        (by
          have h : ((childHL thetaAboveCell000122002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002012) h)
        (by
          have h : ((childHH thetaAboveCell000122002012)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002012) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002013
        (by
          have h : ((childLL thetaAboveCell000122002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002013) h)
        (by
          have h : ((childLH thetaAboveCell000122002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002013) h)
        (by
          have h : ((childHL thetaAboveCell000122002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002013) h)
        (by
          have h : ((childHH thetaAboveCell000122002013)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002013) h))

theorem cover_subtree_39d9268879db :
    adaptiveCoverCheck 8 (childHL (childLL (childHL thetaAboveCell00012200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL thetaAboveCell00012200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002020
        (by
          have h : ((childLL thetaAboveCell000122002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002020) h)
        (by
          have h : ((childLH thetaAboveCell000122002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002020) h)
        (by
          have h : ((childHL thetaAboveCell000122002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002020) h)
        (by
          have h : ((childHH thetaAboveCell000122002020)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002020) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002021
        (by
          have h : ((childLL thetaAboveCell000122002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002021) h)
        (by
          have h : ((childLH thetaAboveCell000122002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002021) h)
        (by
          have h : ((childHL thetaAboveCell000122002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002021) h)
        (by
          have h : ((childHH thetaAboveCell000122002021)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002021) h))
    (by
      have h : (thetaAboveCell000122002022).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002022 h)
    (by
      have h : (thetaAboveCell000122002023).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002023 h)

theorem cover_subtree_39d9037f050e :
    adaptiveCoverCheck 8 (childHH (childLL (childHL thetaAboveCell00012200))) = true := by
  exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL thetaAboveCell00012200)))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002030
        (by
          have h : ((childLL thetaAboveCell000122002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002030) h)
        (by
          have h : ((childLH thetaAboveCell000122002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002030) h)
        (by
          have h : ((childHL thetaAboveCell000122002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002030) h)
        (by
          have h : ((childHH thetaAboveCell000122002030)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002030) h))
    (by
      exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002031
        (by
          have h : ((childLL thetaAboveCell000122002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002031) h)
        (by
          have h : ((childLH thetaAboveCell000122002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002031) h)
        (by
          have h : ((childHL thetaAboveCell000122002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002031) h)
        (by
          have h : ((childHH thetaAboveCell000122002031)).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002031) h))
    (by
      have h : (thetaAboveCell000122002032).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002032 h)
    (by
      have h : (thetaAboveCell000122002033).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002033 h)

theorem e24KC2ThetaAboveLeaf0001220020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012200))
    cover_subtree_bc394da66032
    cover_subtree_0f99148bdc12
    cover_subtree_39d9268879db
    cover_subtree_39d9037f050e
theorem e24KC2ThetaAboveLeaf0001220021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002100 h)
        (by
          have h : (thetaAboveCell000122002101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002101 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002102
            (by
              have h : ((childLL thetaAboveCell000122002102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002102) h)
            (by
              have h : ((childLH thetaAboveCell000122002102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002102) h)
            (by
              have h : ((childHL thetaAboveCell000122002102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002102) h)
            (by
              have h : ((childHH thetaAboveCell000122002102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002102) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002103
            (by
              have h : ((childLL thetaAboveCell000122002103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002103) h)
            (by
              have h : ((childLH thetaAboveCell000122002103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002103) h)
            (by
              have h : ((childHL thetaAboveCell000122002103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002103) h)
            (by
              have h : ((childHH thetaAboveCell000122002103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002103) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002110 h)
        (by
          have h : (thetaAboveCell000122002111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002111 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002112
            (by
              have h : ((childLL thetaAboveCell000122002112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002112) h)
            (by
              have h : ((childLH thetaAboveCell000122002112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002112) h)
            (by
              have h : ((childHL thetaAboveCell000122002112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002112) h)
            (by
              have h : ((childHH thetaAboveCell000122002112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002112) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002113
            (by
              have h : ((childLL thetaAboveCell000122002113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002113) h)
            (by
              have h : ((childLH thetaAboveCell000122002113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002113) h)
            (by
              have h : ((childHL thetaAboveCell000122002113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002113) h)
            (by
              have h : ((childHH thetaAboveCell000122002113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002113) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012200)))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122002120
            (by
              have h : ((childLL thetaAboveCell000122002120)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122002120) h)
            (by
              have h : ((childLH thetaAboveCell000122002120)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122002120) h)
            (by
              have h : ((childHL thetaAboveCell000122002120)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122002120) h)
            (by
              have h : ((childHH thetaAboveCell000122002120)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122002120) h))
        (by
          have h : (thetaAboveCell000122002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002121 h)
        (by
          have h : (thetaAboveCell000122002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002122 h)
        (by
          have h : (thetaAboveCell000122002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002130 h)
        (by
          have h : (thetaAboveCell000122002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002131 h)
        (by
          have h : (thetaAboveCell000122002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002132 h)
        (by
          have h : (thetaAboveCell000122002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002133 h))
theorem e24KC2ThetaAboveLeaf0001220022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002200 h)
        (by
          have h : (thetaAboveCell000122002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002201 h)
        (by
          have h : (thetaAboveCell000122002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002202 h)
        (by
          have h : (thetaAboveCell000122002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002210 h)
        (by
          have h : (thetaAboveCell000122002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002211 h)
        (by
          have h : (thetaAboveCell000122002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002212 h)
        (by
          have h : (thetaAboveCell000122002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002300 h)
        (by
          have h : (thetaAboveCell000122002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002301 h)
        (by
          have h : (thetaAboveCell000122002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002302 h)
        (by
          have h : (thetaAboveCell000122002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002310 h)
        (by
          have h : (thetaAboveCell000122002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002311 h)
        (by
          have h : (thetaAboveCell000122002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002312 h)
        (by
          have h : (thetaAboveCell000122002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003000 h)
        (by
          have h : (thetaAboveCell000122003001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003001 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003002
            (by
              have h : ((childLL thetaAboveCell000122003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003002) h)
            (by
              have h : ((childLH thetaAboveCell000122003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003002) h)
            (by
              have h : ((childHL thetaAboveCell000122003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003002) h)
            (by
              have h : ((childHH thetaAboveCell000122003002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003002) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003003
            (by
              have h : ((childLL thetaAboveCell000122003003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003003) h)
            (by
              have h : ((childLH thetaAboveCell000122003003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003003) h)
            (by
              have h : ((childHL thetaAboveCell000122003003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003003) h)
            (by
              have h : ((childHH thetaAboveCell000122003003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003003) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003010 h)
        (by
          have h : (thetaAboveCell000122003011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003011 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003012
            (by
              have h : ((childLL thetaAboveCell000122003012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003012) h)
            (by
              have h : ((childLH thetaAboveCell000122003012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003012) h)
            (by
              have h : ((childHL thetaAboveCell000122003012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003012) h)
            (by
              have h : ((childHH thetaAboveCell000122003012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003012) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003013
            (by
              have h : ((childLL thetaAboveCell000122003013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003013) h)
            (by
              have h : ((childLH thetaAboveCell000122003013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003013) h)
            (by
              have h : ((childHL thetaAboveCell000122003013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003013) h)
            (by
              have h : ((childHH thetaAboveCell000122003013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003013) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003020 h)
        (by
          have h : (thetaAboveCell000122003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003021 h)
        (by
          have h : (thetaAboveCell000122003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003022 h)
        (by
          have h : (thetaAboveCell000122003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003030 h)
        (by
          have h : (thetaAboveCell000122003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003031 h)
        (by
          have h : (thetaAboveCell000122003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003032 h)
        (by
          have h : (thetaAboveCell000122003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003033 h))
theorem e24KC2ThetaAboveLeaf0001220031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003100 h)
        (by
          have h : (thetaAboveCell000122003101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003101 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003102
            (by
              have h : ((childLL thetaAboveCell000122003102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003102) h)
            (by
              have h : ((childLH thetaAboveCell000122003102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003102) h)
            (by
              have h : ((childHL thetaAboveCell000122003102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003102) h)
            (by
              have h : ((childHH thetaAboveCell000122003102)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003102) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003103
            (by
              have h : ((childLL thetaAboveCell000122003103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003103) h)
            (by
              have h : ((childLH thetaAboveCell000122003103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003103) h)
            (by
              have h : ((childHL thetaAboveCell000122003103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003103) h)
            (by
              have h : ((childHH thetaAboveCell000122003103)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003103) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003110 h)
        (by
          have h : (thetaAboveCell000122003111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003111 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003112
            (by
              have h : ((childLL thetaAboveCell000122003112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003112) h)
            (by
              have h : ((childLH thetaAboveCell000122003112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003112) h)
            (by
              have h : ((childHL thetaAboveCell000122003112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003112) h)
            (by
              have h : ((childHH thetaAboveCell000122003112)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003112) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122003113
            (by
              have h : ((childLL thetaAboveCell000122003113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122003113) h)
            (by
              have h : ((childLH thetaAboveCell000122003113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122003113) h)
            (by
              have h : ((childHL thetaAboveCell000122003113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122003113) h)
            (by
              have h : ((childHH thetaAboveCell000122003113)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122003113) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003120 h)
        (by
          have h : (thetaAboveCell000122003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003121 h)
        (by
          have h : (thetaAboveCell000122003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003122 h)
        (by
          have h : (thetaAboveCell000122003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003130 h)
        (by
          have h : (thetaAboveCell000122003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003131 h)
        (by
          have h : (thetaAboveCell000122003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003132 h)
        (by
          have h : (thetaAboveCell000122003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003133 h))
theorem e24KC2ThetaAboveLeaf0001220032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003200 h)
        (by
          have h : (thetaAboveCell000122003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003201 h)
        (by
          have h : (thetaAboveCell000122003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003202 h)
        (by
          have h : (thetaAboveCell000122003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003210 h)
        (by
          have h : (thetaAboveCell000122003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003211 h)
        (by
          have h : (thetaAboveCell000122003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003212 h)
        (by
          have h : (thetaAboveCell000122003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012200)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012200))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003300 h)
        (by
          have h : (thetaAboveCell000122003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003301 h)
        (by
          have h : (thetaAboveCell000122003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003302 h)
        (by
          have h : (thetaAboveCell000122003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012200)))
        (by
          have h : (thetaAboveCell000122003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003310 h)
        (by
          have h : (thetaAboveCell000122003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003311 h)
        (by
          have h : (thetaAboveCell000122003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003312 h)
        (by
          have h : (thetaAboveCell000122003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012200))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012200)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012200))) h)
theorem e24KC2ThetaAboveLeaf0001220102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012201))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012201))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012201))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012201))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012000 h)
        (by
          have h : (thetaAboveCell000122012001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012001 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122012002
            (by
              have h : ((childLL thetaAboveCell000122012002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122012002) h)
            (by
              have h : ((childLH thetaAboveCell000122012002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122012002) h)
            (by
              have h : ((childHL thetaAboveCell000122012002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122012002) h)
            (by
              have h : ((childHH thetaAboveCell000122012002)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122012002) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122012003
            (by
              have h : ((childLL thetaAboveCell000122012003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122012003) h)
            (by
              have h : ((childLH thetaAboveCell000122012003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122012003) h)
            (by
              have h : ((childHL thetaAboveCell000122012003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122012003) h)
            (by
              have h : ((childHH thetaAboveCell000122012003)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122012003) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012010 h)
        (by
          have h : (thetaAboveCell000122012011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012011 h)
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122012012
            (by
              have h : ((childLL thetaAboveCell000122012012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122012012) h)
            (by
              have h : ((childLH thetaAboveCell000122012012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122012012) h)
            (by
              have h : ((childHL thetaAboveCell000122012012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122012012) h)
            (by
              have h : ((childHH thetaAboveCell000122012012)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122012012) h))
        (by
          exact adaptiveCoverCheck_succ_of_children 6 thetaAboveCell000122012013
            (by
              have h : ((childLL thetaAboveCell000122012013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLL thetaAboveCell000122012013) h)
            (by
              have h : ((childLH thetaAboveCell000122012013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childLH thetaAboveCell000122012013) h)
            (by
              have h : ((childHL thetaAboveCell000122012013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHL thetaAboveCell000122012013) h)
            (by
              have h : ((childHH thetaAboveCell000122012013)).rejected = true := by
                decide +kernel
              exact adaptiveCoverCheck_true_of_rejected 6 (childHH thetaAboveCell000122012013) h)))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012020 h)
        (by
          have h : (thetaAboveCell000122012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012021 h)
        (by
          have h : (thetaAboveCell000122012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012022 h)
        (by
          have h : (thetaAboveCell000122012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012030 h)
        (by
          have h : (thetaAboveCell000122012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012031 h)
        (by
          have h : (thetaAboveCell000122012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012032 h)
        (by
          have h : (thetaAboveCell000122012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012033 h))
theorem e24KC2ThetaAboveLeaf0001220121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012100 h)
        (by
          have h : (thetaAboveCell000122012101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012101 h)
        (by
          have h : (thetaAboveCell000122012102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012102 h)
        (by
          have h : (thetaAboveCell000122012103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012110 h)
        (by
          have h : (thetaAboveCell000122012111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012111 h)
        (by
          have h : (thetaAboveCell000122012112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012112 h)
        (by
          have h : (thetaAboveCell000122012113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012120 h)
        (by
          have h : (thetaAboveCell000122012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012121 h)
        (by
          have h : (thetaAboveCell000122012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012122 h)
        (by
          have h : (thetaAboveCell000122012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012130 h)
        (by
          have h : (thetaAboveCell000122012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012131 h)
        (by
          have h : (thetaAboveCell000122012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012132 h)
        (by
          have h : (thetaAboveCell000122012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012133 h))
theorem e24KC2ThetaAboveLeaf0001220122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012200 h)
        (by
          have h : (thetaAboveCell000122012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012201 h)
        (by
          have h : (thetaAboveCell000122012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012202 h)
        (by
          have h : (thetaAboveCell000122012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012210 h)
        (by
          have h : (thetaAboveCell000122012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012211 h)
        (by
          have h : (thetaAboveCell000122012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012212 h)
        (by
          have h : (thetaAboveCell000122012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012300 h)
        (by
          have h : (thetaAboveCell000122012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012301 h)
        (by
          have h : (thetaAboveCell000122012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012302 h)
        (by
          have h : (thetaAboveCell000122012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012310 h)
        (by
          have h : (thetaAboveCell000122012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012311 h)
        (by
          have h : (thetaAboveCell000122012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012312 h)
        (by
          have h : (thetaAboveCell000122012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013000 h)
        (by
          have h : (thetaAboveCell000122013001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013001 h)
        (by
          have h : (thetaAboveCell000122013002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013002 h)
        (by
          have h : (thetaAboveCell000122013003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013010 h)
        (by
          have h : (thetaAboveCell000122013011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013011 h)
        (by
          have h : (thetaAboveCell000122013012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013012 h)
        (by
          have h : (thetaAboveCell000122013013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013020 h)
        (by
          have h : (thetaAboveCell000122013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013021 h)
        (by
          have h : (thetaAboveCell000122013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013022 h)
        (by
          have h : (thetaAboveCell000122013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013030 h)
        (by
          have h : (thetaAboveCell000122013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013031 h)
        (by
          have h : (thetaAboveCell000122013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013032 h)
        (by
          have h : (thetaAboveCell000122013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013033 h))
theorem e24KC2ThetaAboveLeaf0001220131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013100 h)
        (by
          have h : (thetaAboveCell000122013101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013101 h)
        (by
          have h : (thetaAboveCell000122013102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013102 h)
        (by
          have h : (thetaAboveCell000122013103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013110 h)
        (by
          have h : (thetaAboveCell000122013111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013111 h)
        (by
          have h : (thetaAboveCell000122013112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013112 h)
        (by
          have h : (thetaAboveCell000122013113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013120 h)
        (by
          have h : (thetaAboveCell000122013121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013121 h)
        (by
          have h : (thetaAboveCell000122013122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013122 h)
        (by
          have h : (thetaAboveCell000122013123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013130 h)
        (by
          have h : (thetaAboveCell000122013131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013131 h)
        (by
          have h : (thetaAboveCell000122013132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013132 h)
        (by
          have h : (thetaAboveCell000122013133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013133 h))
theorem e24KC2ThetaAboveLeaf0001220132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013200 h)
        (by
          have h : (thetaAboveCell000122013201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013201 h)
        (by
          have h : (thetaAboveCell000122013202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013202 h)
        (by
          have h : (thetaAboveCell000122013203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013210 h)
        (by
          have h : (thetaAboveCell000122013211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013211 h)
        (by
          have h : (thetaAboveCell000122013212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013212 h)
        (by
          have h : (thetaAboveCell000122013213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001220133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012201)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012201))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013300 h)
        (by
          have h : (thetaAboveCell000122013301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013301 h)
        (by
          have h : (thetaAboveCell000122013302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013302 h)
        (by
          have h : (thetaAboveCell000122013303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012201)))
        (by
          have h : (thetaAboveCell000122013310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013310 h)
        (by
          have h : (thetaAboveCell000122013311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013311 h)
        (by
          have h : (thetaAboveCell000122013312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013312 h)
        (by
          have h : (thetaAboveCell000122013313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122013313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012201))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012201)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012201))) h)
theorem e24KC2ThetaAboveLeaf0001221002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012210))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012210))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012210))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012210))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102000 h)
        (by
          have h : (thetaAboveCell000122102001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102001 h)
        (by
          have h : (thetaAboveCell000122102002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102002 h)
        (by
          have h : (thetaAboveCell000122102003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102010 h)
        (by
          have h : (thetaAboveCell000122102011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102011 h)
        (by
          have h : (thetaAboveCell000122102012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102012 h)
        (by
          have h : (thetaAboveCell000122102013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102020 h)
        (by
          have h : (thetaAboveCell000122102021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102021 h)
        (by
          have h : (thetaAboveCell000122102022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102022 h)
        (by
          have h : (thetaAboveCell000122102023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102030 h)
        (by
          have h : (thetaAboveCell000122102031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102031 h)
        (by
          have h : (thetaAboveCell000122102032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102032 h)
        (by
          have h : (thetaAboveCell000122102033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102033 h))
theorem e24KC2ThetaAboveLeaf0001221021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102100 h)
        (by
          have h : (thetaAboveCell000122102101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102101 h)
        (by
          have h : (thetaAboveCell000122102102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102102 h)
        (by
          have h : (thetaAboveCell000122102103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102110 h)
        (by
          have h : (thetaAboveCell000122102111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102111 h)
        (by
          have h : (thetaAboveCell000122102112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102112 h)
        (by
          have h : (thetaAboveCell000122102113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102120 h)
        (by
          have h : (thetaAboveCell000122102121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102121 h)
        (by
          have h : (thetaAboveCell000122102122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102122 h)
        (by
          have h : (thetaAboveCell000122102123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102130 h)
        (by
          have h : (thetaAboveCell000122102131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102131 h)
        (by
          have h : (thetaAboveCell000122102132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102132 h)
        (by
          have h : (thetaAboveCell000122102133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102133 h))
theorem e24KC2ThetaAboveLeaf0001221022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102200 h)
        (by
          have h : (thetaAboveCell000122102201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102201 h)
        (by
          have h : (thetaAboveCell000122102202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102202 h)
        (by
          have h : (thetaAboveCell000122102203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102210 h)
        (by
          have h : (thetaAboveCell000122102211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102211 h)
        (by
          have h : (thetaAboveCell000122102212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102212 h)
        (by
          have h : (thetaAboveCell000122102213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102300 h)
        (by
          have h : (thetaAboveCell000122102301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102301 h)
        (by
          have h : (thetaAboveCell000122102302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102302 h)
        (by
          have h : (thetaAboveCell000122102303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122102310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102310 h)
        (by
          have h : (thetaAboveCell000122102311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102311 h)
        (by
          have h : (thetaAboveCell000122102312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102312 h)
        (by
          have h : (thetaAboveCell000122102313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122102313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103000 h)
        (by
          have h : (thetaAboveCell000122103001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103001 h)
        (by
          have h : (thetaAboveCell000122103002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103002 h)
        (by
          have h : (thetaAboveCell000122103003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103010 h)
        (by
          have h : (thetaAboveCell000122103011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103011 h)
        (by
          have h : (thetaAboveCell000122103012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103012 h)
        (by
          have h : (thetaAboveCell000122103013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103020 h)
        (by
          have h : (thetaAboveCell000122103021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103021 h)
        (by
          have h : (thetaAboveCell000122103022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103022 h)
        (by
          have h : (thetaAboveCell000122103023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103030 h)
        (by
          have h : (thetaAboveCell000122103031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103031 h)
        (by
          have h : (thetaAboveCell000122103032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103032 h)
        (by
          have h : (thetaAboveCell000122103033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103033 h))
theorem e24KC2ThetaAboveLeaf0001221031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103100 h)
        (by
          have h : (thetaAboveCell000122103101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103101 h)
        (by
          have h : (thetaAboveCell000122103102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103102 h)
        (by
          have h : (thetaAboveCell000122103103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103110 h)
        (by
          have h : (thetaAboveCell000122103111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103111 h)
        (by
          have h : (thetaAboveCell000122103112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103112 h)
        (by
          have h : (thetaAboveCell000122103113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103120 h)
        (by
          have h : (thetaAboveCell000122103121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103121 h)
        (by
          have h : (thetaAboveCell000122103122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103122 h)
        (by
          have h : (thetaAboveCell000122103123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103130 h)
        (by
          have h : (thetaAboveCell000122103131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103131 h)
        (by
          have h : (thetaAboveCell000122103132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103132 h)
        (by
          have h : (thetaAboveCell000122103133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103133 h))
theorem e24KC2ThetaAboveLeaf0001221032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103200 h)
        (by
          have h : (thetaAboveCell000122103201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103201 h)
        (by
          have h : (thetaAboveCell000122103202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103202 h)
        (by
          have h : (thetaAboveCell000122103203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103210 h)
        (by
          have h : (thetaAboveCell000122103211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103211 h)
        (by
          have h : (thetaAboveCell000122103212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103212 h)
        (by
          have h : (thetaAboveCell000122103213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012210)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012210))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103300 h)
        (by
          have h : (thetaAboveCell000122103301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103301 h)
        (by
          have h : (thetaAboveCell000122103302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103302 h)
        (by
          have h : (thetaAboveCell000122103303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012210)))
        (by
          have h : (thetaAboveCell000122103310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103310 h)
        (by
          have h : (thetaAboveCell000122103311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103311 h)
        (by
          have h : (thetaAboveCell000122103312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103312 h)
        (by
          have h : (thetaAboveCell000122103313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122103313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012210))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012210)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012210))) h)
theorem e24KC2ThetaAboveLeaf0001221102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012211))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012211))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012211))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012211))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112000 h)
        (by
          have h : (thetaAboveCell000122112001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112001 h)
        (by
          have h : (thetaAboveCell000122112002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112002 h)
        (by
          have h : (thetaAboveCell000122112003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112010 h)
        (by
          have h : (thetaAboveCell000122112011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112011 h)
        (by
          have h : (thetaAboveCell000122112012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112012 h)
        (by
          have h : (thetaAboveCell000122112013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112020 h)
        (by
          have h : (thetaAboveCell000122112021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112021 h)
        (by
          have h : (thetaAboveCell000122112022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112022 h)
        (by
          have h : (thetaAboveCell000122112023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112030 h)
        (by
          have h : (thetaAboveCell000122112031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112031 h)
        (by
          have h : (thetaAboveCell000122112032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112032 h)
        (by
          have h : (thetaAboveCell000122112033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112033 h))
theorem e24KC2ThetaAboveLeaf0001221121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112100 h)
        (by
          have h : (thetaAboveCell000122112101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112101 h)
        (by
          have h : (thetaAboveCell000122112102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112102 h)
        (by
          have h : (thetaAboveCell000122112103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112110 h)
        (by
          have h : (thetaAboveCell000122112111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112111 h)
        (by
          have h : (thetaAboveCell000122112112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112112 h)
        (by
          have h : (thetaAboveCell000122112113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112120 h)
        (by
          have h : (thetaAboveCell000122112121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112121 h)
        (by
          have h : (thetaAboveCell000122112122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112122 h)
        (by
          have h : (thetaAboveCell000122112123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112130 h)
        (by
          have h : (thetaAboveCell000122112131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112131 h)
        (by
          have h : (thetaAboveCell000122112132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112132 h)
        (by
          have h : (thetaAboveCell000122112133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112133 h))
theorem e24KC2ThetaAboveLeaf0001221122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112200 h)
        (by
          have h : (thetaAboveCell000122112201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112201 h)
        (by
          have h : (thetaAboveCell000122112202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112202 h)
        (by
          have h : (thetaAboveCell000122112203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112210 h)
        (by
          have h : (thetaAboveCell000122112211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112211 h)
        (by
          have h : (thetaAboveCell000122112212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112212 h)
        (by
          have h : (thetaAboveCell000122112213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112300 h)
        (by
          have h : (thetaAboveCell000122112301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112301 h)
        (by
          have h : (thetaAboveCell000122112302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112302 h)
        (by
          have h : (thetaAboveCell000122112303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122112310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112310 h)
        (by
          have h : (thetaAboveCell000122112311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112311 h)
        (by
          have h : (thetaAboveCell000122112312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112312 h)
        (by
          have h : (thetaAboveCell000122112313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122112313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113000 h)
        (by
          have h : (thetaAboveCell000122113001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113001 h)
        (by
          have h : (thetaAboveCell000122113002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113002 h)
        (by
          have h : (thetaAboveCell000122113003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113010 h)
        (by
          have h : (thetaAboveCell000122113011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113011 h)
        (by
          have h : (thetaAboveCell000122113012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113012 h)
        (by
          have h : (thetaAboveCell000122113013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113020 h)
        (by
          have h : (thetaAboveCell000122113021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113021 h)
        (by
          have h : (thetaAboveCell000122113022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113022 h)
        (by
          have h : (thetaAboveCell000122113023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113030 h)
        (by
          have h : (thetaAboveCell000122113031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113031 h)
        (by
          have h : (thetaAboveCell000122113032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113032 h)
        (by
          have h : (thetaAboveCell000122113033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113033 h))
theorem e24KC2ThetaAboveLeaf0001221131 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113100 h)
        (by
          have h : (thetaAboveCell000122113101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113101 h)
        (by
          have h : (thetaAboveCell000122113102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113102 h)
        (by
          have h : (thetaAboveCell000122113103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113110 h)
        (by
          have h : (thetaAboveCell000122113111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113111 h)
        (by
          have h : (thetaAboveCell000122113112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113112 h)
        (by
          have h : (thetaAboveCell000122113113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113120 h)
        (by
          have h : (thetaAboveCell000122113121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113121 h)
        (by
          have h : (thetaAboveCell000122113122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113122 h)
        (by
          have h : (thetaAboveCell000122113123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113130 h)
        (by
          have h : (thetaAboveCell000122113131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113131 h)
        (by
          have h : (thetaAboveCell000122113132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113132 h)
        (by
          have h : (thetaAboveCell000122113133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113133 h))
theorem e24KC2ThetaAboveLeaf0001221132 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113200 h)
        (by
          have h : (thetaAboveCell000122113201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113201 h)
        (by
          have h : (thetaAboveCell000122113202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113202 h)
        (by
          have h : (thetaAboveCell000122113203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113210 h)
        (by
          have h : (thetaAboveCell000122113211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113211 h)
        (by
          have h : (thetaAboveCell000122113212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113212 h)
        (by
          have h : (thetaAboveCell000122113213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001221133 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012211)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012211))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113300 h)
        (by
          have h : (thetaAboveCell000122113301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113301 h)
        (by
          have h : (thetaAboveCell000122113302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113302 h)
        (by
          have h : (thetaAboveCell000122113303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012211)))
        (by
          have h : (thetaAboveCell000122113310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113310 h)
        (by
          have h : (thetaAboveCell000122113311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113311 h)
        (by
          have h : (thetaAboveCell000122113312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113312 h)
        (by
          have h : (thetaAboveCell000122113313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000122113313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012211))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012211)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012211))) h)
theorem e24KC2ThetaAboveLeaf0001230002 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012300))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230003 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012300))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230012 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012300))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230013 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012300))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230020 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002000 h)
        (by
          have h : (thetaAboveCell000123002001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002001 h)
        (by
          have h : (thetaAboveCell000123002002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002002 h)
        (by
          have h : (thetaAboveCell000123002003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002010 h)
        (by
          have h : (thetaAboveCell000123002011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002011 h)
        (by
          have h : (thetaAboveCell000123002012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002012 h)
        (by
          have h : (thetaAboveCell000123002013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002020 h)
        (by
          have h : (thetaAboveCell000123002021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002021 h)
        (by
          have h : (thetaAboveCell000123002022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002022 h)
        (by
          have h : (thetaAboveCell000123002023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002030 h)
        (by
          have h : (thetaAboveCell000123002031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002031 h)
        (by
          have h : (thetaAboveCell000123002032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002032 h)
        (by
          have h : (thetaAboveCell000123002033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002033 h))
theorem e24KC2ThetaAboveLeaf0001230021 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002100 h)
        (by
          have h : (thetaAboveCell000123002101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002101 h)
        (by
          have h : (thetaAboveCell000123002102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002102 h)
        (by
          have h : (thetaAboveCell000123002103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002110 h)
        (by
          have h : (thetaAboveCell000123002111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002111 h)
        (by
          have h : (thetaAboveCell000123002112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002112 h)
        (by
          have h : (thetaAboveCell000123002113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002120 h)
        (by
          have h : (thetaAboveCell000123002121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002121 h)
        (by
          have h : (thetaAboveCell000123002122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002122 h)
        (by
          have h : (thetaAboveCell000123002123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002130 h)
        (by
          have h : (thetaAboveCell000123002131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002131 h)
        (by
          have h : (thetaAboveCell000123002132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002132 h)
        (by
          have h : (thetaAboveCell000123002133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002133 h))
theorem e24KC2ThetaAboveLeaf0001230022 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002200 h)
        (by
          have h : (thetaAboveCell000123002201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002201 h)
        (by
          have h : (thetaAboveCell000123002202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002202 h)
        (by
          have h : (thetaAboveCell000123002203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002210 h)
        (by
          have h : (thetaAboveCell000123002211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002211 h)
        (by
          have h : (thetaAboveCell000123002212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002212 h)
        (by
          have h : (thetaAboveCell000123002213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230023 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002300 h)
        (by
          have h : (thetaAboveCell000123002301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002301 h)
        (by
          have h : (thetaAboveCell000123002302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002302 h)
        (by
          have h : (thetaAboveCell000123002303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123002310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002310 h)
        (by
          have h : (thetaAboveCell000123002311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002311 h)
        (by
          have h : (thetaAboveCell000123002312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002312 h)
        (by
          have h : (thetaAboveCell000123002313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123002313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230030 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003000 h)
        (by
          have h : (thetaAboveCell000123003001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003001 h)
        (by
          have h : (thetaAboveCell000123003002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003002 h)
        (by
          have h : (thetaAboveCell000123003003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003010 h)
        (by
          have h : (thetaAboveCell000123003011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003011 h)
        (by
          have h : (thetaAboveCell000123003012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003012 h)
        (by
          have h : (thetaAboveCell000123003013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003020 h)
        (by
          have h : (thetaAboveCell000123003021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003021 h)
        (by
          have h : (thetaAboveCell000123003022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003022 h)
        (by
          have h : (thetaAboveCell000123003023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003030 h)
        (by
          have h : (thetaAboveCell000123003031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003031 h)
        (by
          have h : (thetaAboveCell000123003032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003032 h)
        (by
          have h : (thetaAboveCell000123003033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003033 h))
theorem e24KC2ThetaAboveLeaf0001230031 :
    adaptiveCoverCheck 9 (childLH (childHH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHH thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003100 h)
        (by
          have h : (thetaAboveCell000123003101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003101 h)
        (by
          have h : (thetaAboveCell000123003102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003102 h)
        (by
          have h : (thetaAboveCell000123003103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003110 h)
        (by
          have h : (thetaAboveCell000123003111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003111 h)
        (by
          have h : (thetaAboveCell000123003112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003112 h)
        (by
          have h : (thetaAboveCell000123003113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003120 h)
        (by
          have h : (thetaAboveCell000123003121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003121 h)
        (by
          have h : (thetaAboveCell000123003122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003122 h)
        (by
          have h : (thetaAboveCell000123003123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003130 h)
        (by
          have h : (thetaAboveCell000123003131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003131 h)
        (by
          have h : (thetaAboveCell000123003132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003132 h)
        (by
          have h : (thetaAboveCell000123003133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003133 h))
theorem e24KC2ThetaAboveLeaf0001230032 :
    adaptiveCoverCheck 9 (childHL (childHH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHH thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003200 h)
        (by
          have h : (thetaAboveCell000123003201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003201 h)
        (by
          have h : (thetaAboveCell000123003202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003202 h)
        (by
          have h : (thetaAboveCell000123003203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003210 h)
        (by
          have h : (thetaAboveCell000123003211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003211 h)
        (by
          have h : (thetaAboveCell000123003212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003212 h)
        (by
          have h : (thetaAboveCell000123003213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003213 h))
    (by
      have h : ((childHL (childHL (childHH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHL (childHH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHH
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230033 :
    adaptiveCoverCheck 9 (childHH (childHH thetaAboveCell00012300)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHH thetaAboveCell00012300))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003300 h)
        (by
          have h : (thetaAboveCell000123003301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003301 h)
        (by
          have h : (thetaAboveCell000123003302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003302 h)
        (by
          have h : (thetaAboveCell000123003303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHH
        thetaAboveCell00012300)))
        (by
          have h : (thetaAboveCell000123003310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003310 h)
        (by
          have h : (thetaAboveCell000123003311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003311 h)
        (by
          have h : (thetaAboveCell000123003312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003312 h)
        (by
          have h : (thetaAboveCell000123003313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123003313 h))
    (by
      have h : ((childHL (childHH (childHH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHH
        thetaAboveCell00012300))) h)
    (by
      have h : ((childHH (childHH (childHH thetaAboveCell00012300)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHH
        thetaAboveCell00012300))) h)
theorem e24KC2ThetaAboveLeaf0001230102 :
    adaptiveCoverCheck 9 (childHL (childLL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLL thetaAboveCell00012301))
    (by
      have h : ((childLL (childHL (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childLH (childHL (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHL (childHL (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHL (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLL
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230103 :
    adaptiveCoverCheck 9 (childHH (childLL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLL thetaAboveCell00012301))
    (by
      have h : ((childLL (childHH (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childLH (childHH (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHL (childHH (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHH (childLL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLL
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230112 :
    adaptiveCoverCheck 9 (childHL (childLH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childLH thetaAboveCell00012301))
    (by
      have h : ((childLL (childHL (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHL (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childLH (childHL (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHL (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHL (childHL (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHL (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childLH
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230113 :
    adaptiveCoverCheck 9 (childHH (childLH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childLH thetaAboveCell00012301))
    (by
      have h : ((childLL (childHH (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLL (childHH (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childLH (childHH (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childLH (childHH (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHL (childHH (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childLH
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHH (childLH thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childLH
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230120 :
    adaptiveCoverCheck 9 (childLL (childHL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHL thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012000 h)
        (by
          have h : (thetaAboveCell000123012001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012001 h)
        (by
          have h : (thetaAboveCell000123012002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012002 h)
        (by
          have h : (thetaAboveCell000123012003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012010 h)
        (by
          have h : (thetaAboveCell000123012011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012011 h)
        (by
          have h : (thetaAboveCell000123012012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012012 h)
        (by
          have h : (thetaAboveCell000123012013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012020 h)
        (by
          have h : (thetaAboveCell000123012021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012021 h)
        (by
          have h : (thetaAboveCell000123012022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012022 h)
        (by
          have h : (thetaAboveCell000123012023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012030 h)
        (by
          have h : (thetaAboveCell000123012031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012031 h)
        (by
          have h : (thetaAboveCell000123012032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012032 h)
        (by
          have h : (thetaAboveCell000123012033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012033 h))
theorem e24KC2ThetaAboveLeaf0001230121 :
    adaptiveCoverCheck 9 (childLH (childHL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLH (childHL thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012100).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012100 h)
        (by
          have h : (thetaAboveCell000123012101).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012101 h)
        (by
          have h : (thetaAboveCell000123012102).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012102 h)
        (by
          have h : (thetaAboveCell000123012103).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012103 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012110).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012110 h)
        (by
          have h : (thetaAboveCell000123012111).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012111 h)
        (by
          have h : (thetaAboveCell000123012112).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012112 h)
        (by
          have h : (thetaAboveCell000123012113).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012113 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012120).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012120 h)
        (by
          have h : (thetaAboveCell000123012121).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012121 h)
        (by
          have h : (thetaAboveCell000123012122).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012122 h)
        (by
          have h : (thetaAboveCell000123012123).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012123 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012130).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012130 h)
        (by
          have h : (thetaAboveCell000123012131).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012131 h)
        (by
          have h : (thetaAboveCell000123012132).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012132 h)
        (by
          have h : (thetaAboveCell000123012133).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012133 h))
theorem e24KC2ThetaAboveLeaf0001230122 :
    adaptiveCoverCheck 9 (childHL (childHL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHL (childHL thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012200).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012200 h)
        (by
          have h : (thetaAboveCell000123012201).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012201 h)
        (by
          have h : (thetaAboveCell000123012202).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012202 h)
        (by
          have h : (thetaAboveCell000123012203).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012203 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHL (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012210).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012210 h)
        (by
          have h : (thetaAboveCell000123012211).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012211 h)
        (by
          have h : (thetaAboveCell000123012212).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012212 h)
        (by
          have h : (thetaAboveCell000123012213).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012213 h))
    (by
      have h : ((childHL (childHL (childHL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHL (childHL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHL (childHL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHL (childHL
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230123 :
    adaptiveCoverCheck 9 (childHH (childHL thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childHH (childHL thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childHH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012300).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012300 h)
        (by
          have h : (thetaAboveCell000123012301).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012301 h)
        (by
          have h : (thetaAboveCell000123012302).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012302 h)
        (by
          have h : (thetaAboveCell000123012303).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012303 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childHH (childHL
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123012310).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012310 h)
        (by
          have h : (thetaAboveCell000123012311).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012311 h)
        (by
          have h : (thetaAboveCell000123012312).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012312 h)
        (by
          have h : (thetaAboveCell000123012313).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123012313 h))
    (by
      have h : ((childHL (childHH (childHL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHL (childHH (childHL
        thetaAboveCell00012301))) h)
    (by
      have h : ((childHH (childHH (childHL thetaAboveCell00012301)))).rejected = true := by
        decide +kernel
      exact adaptiveCoverCheck_true_of_rejected 8 (childHH (childHH (childHL
        thetaAboveCell00012301))) h)
theorem e24KC2ThetaAboveLeaf0001230130 :
    adaptiveCoverCheck 9 (childLL (childHH thetaAboveCell00012301)) = true := by
  exact adaptiveCoverCheck_succ_of_children 8 (childLL (childHH thetaAboveCell00012301))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLL (childLL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013000).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013000 h)
        (by
          have h : (thetaAboveCell000123013001).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013001 h)
        (by
          have h : (thetaAboveCell000123013002).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013002 h)
        (by
          have h : (thetaAboveCell000123013003).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013003 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childLH (childLL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013010).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013010 h)
        (by
          have h : (thetaAboveCell000123013011).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013011 h)
        (by
          have h : (thetaAboveCell000123013012).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013012 h)
        (by
          have h : (thetaAboveCell000123013013).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013013 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHL (childLL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013020).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013020 h)
        (by
          have h : (thetaAboveCell000123013021).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013021 h)
        (by
          have h : (thetaAboveCell000123013022).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013022 h)
        (by
          have h : (thetaAboveCell000123013023).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013023 h))
    (by
      exact adaptiveCoverCheck_succ_of_children 7 (childHH (childLL (childHH
        thetaAboveCell00012301)))
        (by
          have h : (thetaAboveCell000123013030).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013030 h)
        (by
          have h : (thetaAboveCell000123013031).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013031 h)
        (by
          have h : (thetaAboveCell000123013032).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013032 h)
        (by
          have h : (thetaAboveCell000123013033).rejected = true := by
            decide +kernel
          exact adaptiveCoverCheck_true_of_rejected 7 thetaAboveCell000123013033 h))

end PartE
end GerverSofa

end

end

end

end

end

end
