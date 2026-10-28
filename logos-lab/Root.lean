-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
/-
  Root — entry point. Imports everything.

  Phase 1: MEASURES.md (measures stated before code), syntax +
  unification, explicit State / Resolve transition system, cut
  lemma, measures, guards, finiteness enumeration, example data.
  Phase 2: Deriv, solve (fuel recursion, guards inside), kernel
  checker (trace replay), replay_sound, checker_sound,
  solve_terminates, and the burglary/alarm #eval pipeline below.

  Still BLOCKED (see STATUS.md): theorems 3-6, alp_loop,
  unify_sound (semantic), full ISO cut propagation in solve,
  and the finiteness theorem. They are not printed here because
  they do not exist as proved theorems yet.
-/
import LogosLab

open LogosLab

#print axioms cut_lemma
#print axioms step_deterministic
#print axioms step_cut
#print axioms extendBudget_lt
#print axioms mu_empty
#print axioms replay_sound
#print axioms checker_sound
#print axioms solve_terminates
#print axioms replayTrace_sound
#print axioms erase_length_lt
#print axioms lookup_bind
#print axioms applySubst_const
#print axioms applySubst_var_unbound

/-- Burglary/alarm pipeline, end to end, entropy guard active.
    Initial state: goal alarm, no hypotheses yet.
    With weight threshold T = 3 (burglary weight 3, earthquake
    weight 2), both minimal explanations are returned.
    With T = 2, only earthquake survives (burglary pruned). -/
def burglaryInit : State :=
  { goals := [Goal.atom { pred := "alarm", args := [] }], subst := [],
    depth := 0, cutBarrier := 0, alternatives := [], abduced := [] }

#eval solve 10 burglaryProgram burglaryAbducibles (weightGuard burglaryWeight 3) burglaryInit
#eval solve 10 burglaryProgram burglaryAbducibles (weightGuard burglaryWeight 2) burglaryInit
