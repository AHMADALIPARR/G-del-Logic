/-
  LogosLab.Measures — termination measures. See MEASURES.md §4.
  No solver code is defined here: `solve` and `alp_loop` are
  FUTURE signatures, stated in MEASURES.md, not in code. What IS
  defined here are the measure functions and the one measure lemma
  that is already provable: budget strictly decreases on extension.
-/

import LogosLab.State

namespace LogosLab

/-- mu(explanation) = number of abducible literals + total term size.
    Since atomSize = argument count in this fragment, this is
    Δ.length + total argument count. -/
def mu (Δ : List Atom) : Nat :=
  Δ.length + (Δ.map atomSize).foldr (· + ·) 0

/-- mu of the empty explanation is 0. -/
theorem mu_empty : mu [] = 0 :=
  rfl

/-- Measure of a state for solver-phase bookkeeping: resolvent size
    plus depth. This is NOT the solver's termination measure — fuel
    is (see MEASURES.md §4). It is provided so the solver phase can
    state invariants about resolvent size without redefining it. -/
def stateMeasure (st : State) : Nat :=
  resolventSize st.goals + st.depth

/-- Remaining hypothesis-count budget. -/
abbrev Budget := Nat

/-- The abductive extension rule may only move to a strictly smaller
    remaining budget. -/
def extendBudget (b : Budget) : Budget :=
  b - 1

/-- Budget strictly decreases on extension, whenever there is budget
    to spend. Proved by omega. -/
theorem extendBudget_lt (b : Budget) (hb : b ≠ 0) :
    extendBudget b < b := by
  cases b with
  | zero => contradiction
  | succ n => simp [extendBudget]

end LogosLab
