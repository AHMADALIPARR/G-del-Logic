-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
/-
  LogosLab.Examples — program DATA for the solver phase.
  This file contains no solver, no answers, and no pipeline run.
  It exists so the solver phase has a fixed, named example to run:
  the burglary/alarm ALP example, with the entropy guard's weight
  function. Claiming a pipeline result from this file alone would
  be fabrication; see STATUS.md.
-/

import LogosLab.Guards

namespace LogosLab

/-- Burglary/alarm program (data only):
    alarm :- burglary.
    alarm :- earthquake.
    Observation (future solver input): alarm. -/
def burglaryProgram : Program :=
  [ { head := { pred := "alarm", args := [] },
      body := [Goal.atom { pred := "burglary", args := [] }] },
    { head := { pred := "alarm", args := [] },
      body := [Goal.atom { pred := "earthquake", args := [] }] } ]

/-- Abducibles for the burglary example (data only). -/
def burglaryAbducibles : List Atom :=
  [ { pred := "burglary", args := [] },
    { pred := "earthquake", args := [] } ]

/-- Scaled entropy weights for the burglary example (data only):
    burglary = 3 units, earthquake = 2 units, everything else = 10.
    The weight guard threshold T is chosen by the solver phase;
    no threshold is asserted here. -/
def burglaryWeight : Atom -> Weight :=
  fun a => if a.pred = "burglary" then 3
           else if a.pred = "earthquake" then 2
           else 10

end LogosLab
