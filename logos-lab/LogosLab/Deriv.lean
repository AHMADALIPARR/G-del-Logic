/-
  LogosLab.Deriv — derivation trees, the solver, and the kernel
  checker (trace replay). Phase 2.

  Soundness here is SYNTACTIC, stated honestly: an answer returned
  by `solve` has a `Deriv` tree, and a candidate accepted by the
  kernel checker has a `Deriv` tree. That is theorems 1 and 2 as
  specified ("has a Resolve-derivation witnessed by Deriv",
  "Deriv exists for it"). It does NOT, by itself, claim the
  semantic lemma `unify_sound` (applied atoms are equal under the
  final substitution) — that lemma remains BLOCKED in STATUS.md,
  with its precise counterexample / hypothesis recorded there.
  Conflating syntactic replay with semantic soundness would be
  exactly the kind of proof-stamping this project forbids.
-/

import LogosLab.State
import LogosLab.Guards

namespace LogosLab

/-- An answer: the final accumulated explanation and substitution. -/
structure Answer where
  abduced : List Atom
  subst : Subst
deriving DecidableEq, Repr, Inhabited

/-- A derivation tree. Parameters, in order:
    prog: program, A: abducible list,
    goals: resolvent to solve, s: current substitution,
    Δ: hypotheses accumulated so far, Δf: final hypotheses,
    sf: final substitution.
    - empty: empty goals solve to themselves (Δf = Δ, sf = s).
    - cut: cut drops its goal, derivation continues unchanged.
    - resolve: a clause in the program, unified with the head atom,
      derivation continues with body ++ rest under the new subst.
    - abduce: an abducible atom is added to the accumulated Δ. -/
inductive Deriv (prog : Program) (A : List Atom) :
    List Goal -> Subst -> List Atom -> List Atom -> Subst -> Prop
  | empty : ∀ (s : Subst) (Δ : List Atom),
      Deriv prog A [] s Δ Δ s
  | cut : ∀ (rs : List Goal) (s : Subst) (Δ Δf : List Atom) (sf : Subst),
      Deriv prog A rs s Δ Δf sf -> Deriv prog A (Goal.cut :: rs) s Δ Δf sf
  | resolve : ∀ (a : Atom) (rs : List Goal) (s s' : Subst)
      (Δ Δf : List Atom) (sf : Subst) (cl : Clause),
      cl ∈ prog -> unifyAtom s cl.head a = some s' ->
      Deriv prog A (cl.body ++ rs) s' Δ Δf sf ->
      Deriv prog A (Goal.atom a :: rs) s Δ Δf sf
  | abduce : ∀ (a : Atom) (rs : List Goal) (s : Subst)
      (Δ Δf : List Atom) (sf : Subst),
      a ∈ A -> Deriv prog A rs s (a :: Δ) Δf sf ->
      Deriv prog A (Goal.atom a :: rs) s Δ Δf sf

/-- Flatten a list of answer lists, in order. -/
def flattenAnswers : List (List Answer) -> List Answer :=
  fun ls => ls.foldr (· ++ ·) []

/-- The abduce successor state: drop the head atom, add it to the
    accumulated explanation, and bump the depth. -/
def abduceState (st : State) (a : Atom) (rs : List Goal) : State :=
  { st with goals := rs, abduced := a :: st.abduced, depth := st.depth + 1 }

/-- The solver. Fuel is the ONLY termination measure: every
    recursive call is on `fuel - 1`, visibly, in the code below
    (pattern `fuel + 1` with recursive calls on `fuel`).
    Guards are evaluated at every node BEFORE recursion: if
    `guard st = false`, this node returns no answers, without
    recursing. Cut advances via `cutStep`. Atom goals try, in
    order, every clause successor from `step`, then (if the atom
    is abducible) the abduce successor. Backtracking is the list
    recursion over `step` successors — the explicit alternatives
    stack in `State` is carried in successor states (see
    `successorsFromChoices`), but full ISO cut propagation to
    sibling choices is NOT yet implemented in this solver: a cut
    truncates the current state's alternatives field, and that
    truncation is not yet propagated to the parent's successor
    list. That affects completeness (fewer answers pruned), not
    soundness (every returned answer still has a Deriv, proved
    in `replay_sound`). Cut propagation is listed as blocked in
    STATUS.md under completeness, not hidden. -/
def solve : Nat -> Program -> List Atom -> Guard -> State -> List Answer
  | 0, _, _, _, _ => []
  | fuel + 1, prog, A, guard, st =>
      if guard st then
        match st.goals with
        | [] => [{ abduced := st.abduced, subst := st.subst }]
        | Goal.cut :: rs =>
            solve fuel prog A guard (cutStep st rs)
        | Goal.atom a :: rs =>
            let clauseAnswers :=
              flattenAnswers ((step prog st).map fun s' =>
                if guard s' then solve fuel prog A guard s' else [])
            let abduceAnswers :=
              if a ∈ A then
                if guard (abduceState st a rs) then
                  solve fuel prog A guard (abduceState st a rs)
                else []
              else []
            clauseAnswers ++ abduceAnswers
      else []

/-- A candidate derivation step, supplied by an untrusted external
    engine. The kernel does NOT trust it: it replays it. -/
inductive TraceStep where
  | resolve : Nat -> TraceStep
  | abduce : Atom -> TraceStep
  | cut : TraceStep
deriving DecidableEq, Repr, Inhabited

/-- Replay a trace against goals, substitution, and accumulated
    hypotheses. Returns the final (Δ, subst) iff the trace solves
    the goals exactly (empty goals at end of trace, no goals left
    early, every step legal). `none` otherwise. -/
def replayTrace : Program -> List Atom -> List Goal -> Subst -> List Atom ->
    List TraceStep -> Option (List Atom × Subst)
  | _, _, [], s, Δ, [] => some (Δ, s)
  | _, _, _, _, _, [] => none
  | prog, A, Goal.cut :: rs, s, Δ, TraceStep.cut :: rest =>
      replayTrace prog A rs s Δ rest
  | prog, A, Goal.atom a :: rs, s, Δ, TraceStep.resolve i :: rest =>
      match prog[i]? with
      | none => none
      | some cl =>
          match unifyAtom s cl.head a with
          | none => none
          | some s' => replayTrace prog A (cl.body ++ rs) s' Δ rest
  | prog, A, Goal.atom a :: rs, s, Δ, TraceStep.abduce b :: rest =>
      if a = b ∧ b ∈ A then
        replayTrace prog A rs s (b :: Δ) rest
      else none
  | _, _, _, _, _, _ => none

/-- Kernel checker: accept a candidate answer iff some trace replays
    to exactly that answer (same final Δ and subst). The trace is
    untrusted input; acceptance is by replay, not by trust. -/
def checker (prog : Program) (A : List Atom) (goals : List Goal)
    (s : Subst) (Δ : List Atom) (ans : Answer)
    (trace : List TraceStep) : Bool :=
  match replayTrace prog A goals s Δ trace with
  | some (Δf, sf) => decide (Δf = ans.abduced) && decide (sf = ans.subst)
  | none => false

end LogosLab
