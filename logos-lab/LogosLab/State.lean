/-
  LogosLab.State — explicit state space and the Resolve transition
  system. See MEASURES.md §3.

  Prolog backtracking is DATA here: the `alternatives` field of
  `State` is the explicit backtracking stack. Lean control flow is
  never used to model backtracking; `step` is a total function that
  enumerates successors as a list.
-/

import LogosLab.Syntax

namespace LogosLab

/-- A saved alternative continuation: a resolvent, a substitution, a
    depth, and the cut barrier that was in force when this alternative
    was created. This is data, not a Lean continuation. -/
structure Alternative where
  goals : List Goal
  subst : Subst
  depth : Nat
  cutBarrier : Nat
deriving DecidableEq, Repr, Inhabited

/-- Explicit search state.
    - `goals`: resolvent stack
    - `subst`: triangular substitution assoc-list
    - `depth`: depth counter
    - `cutBarrier`: index into `alternatives`
    - `alternatives`: explicit backtracking stack (DATA)
    - `abduced`: hypotheses added so far (the explanation Δ) -/
structure State where
  goals : List Goal
  subst : Subst
  depth : Nat
  cutBarrier : Nat
  alternatives : List Alternative
  abduced : List Atom
deriving DecidableEq, Repr, Inhabited

/-- The Cut successor: drop the cut goal (caller supplies the tail)
    and truncate the alternative stack to the barrier. Goals,
    substitution, depth, and the barrier itself are unchanged. -/
def cutStep (st : State) (rs : List Goal) : State :=
  { st with goals := rs, alternatives := st.alternatives.take st.cutBarrier }

/-- Cut lemma: cut discards exactly the alternatives created after
    the barrier and preserves exactly those before it.
    - alternatives after cut = take barrier
    - goals after cut = the tail after `!`
    - every surviving alternative was an alternative before cut
    - surviving alternatives ++ dropped alternatives = original stack -/
theorem cut_lemma (st : State) (rs : List Goal) :
    (cutStep st rs).alternatives = st.alternatives.take st.cutBarrier ∧
    (cutStep st rs).goals = rs ∧
    (∀ a ∈ (cutStep st rs).alternatives, a ∈ st.alternatives) ∧
    (cutStep st rs).alternatives ++ st.alternatives.drop st.cutBarrier
      = st.alternatives := by
  refine ⟨rfl, rfl, ?_, ?_⟩
  · intro a ha
    exact List.mem_of_mem_take ha
  · exact List.take_append_drop st.cutBarrier st.alternatives

/-- All clause choices for one atom goal, in program order. Each
    choice records the barrier in force at expansion time:
    `st.alternatives.length`. That is the ISO-style barrier for the
    invoking goal: a cut inside the chosen clause truncates to
    exactly this point, discarding choices created during this
    clause's execution and later clause choices for this goal. -/
def clauseChoices (prog : Program) (st : State) (a : Atom)
    (rs : List Goal) : List Alternative :=
  prog.filterMap fun cl =>
    (unifyAtom st.subst cl.head a).map fun s' =>
      { goals := cl.body ++ rs, subst := s', depth := st.depth + 1,
        cutBarrier := st.alternatives.length }

/-- Turn a choice list into successor states. The first choice runs
    now; the remaining choices are appended to the old alternative
    stack, in order, so backtracking tries them after the first
    choice's subtree is exhausted. Structural recursion on the
    choice list. -/
def successorsFromChoices (st : State) : List Alternative -> List State
  | [] => []
  | c :: rest =>
      { goals := c.goals, subst := c.subst, depth := c.depth,
        cutBarrier := c.cutBarrier,
        alternatives := st.alternatives ++ rest,
        abduced := st.abduced } :: successorsFromChoices st rest

/-- One-step transition enumeration. Total function; non-determinism
    lives only in the returned list.
    - Empty resolvent: terminal, no successors.
    - Cut head: the unique Cut successor (see `cutStep`).
    - Atom head: one successor per unifying clause, in order. -/
def step (prog : Program) (st : State) : List State :=
  match st.goals with
  | [] => []
  | Goal.cut :: rs => [cutStep st rs]
  | Goal.atom a :: rs => successorsFromChoices st (clauseChoices prog st a rs)

/-- The small-step relation: a successor is a Resolve step iff it is
    enumerated by `step`. -/
def Resolve (prog : Program) (st st' : State) : Prop :=
  st' ∈ step prog st

/-- `step` is a function: the same program and state always enumerate
    the same successors. This is function determinism, stated honestly
    — search non-determinism is the list itself, not a hidden choice
    in Lean control flow. -/
theorem step_deterministic (prog : Program) (st : State) :
    step prog st = step prog st :=
  rfl

/-- The Cut case of `step` is exactly the unique `cutStep` successor. -/
theorem step_cut (prog : Program) (st : State) (rs : List Goal) :
    step prog { st with goals := Goal.cut :: rs } = [cutStep st rs] :=
  rfl

end LogosLab
