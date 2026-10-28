# MEASURES.md — logos-lab, Phase 1

This file states every measure and guard BEFORE the code that uses it.
It is written first, per the mission brief: no solver code exists yet
in this phase (see STATUS.md). Types below are the exact types used
in `LogosLab/*.lean`, or, where marked FUTURE, the exact signature
the next phase must implement — not a paraphrase.

## 0. Scope decisions (load-bearing, read first)

- Fragment: Datalog-style Horn clauses. Terms are `Var Nat | Const Nat`
  — no function symbols. This is deliberate, not a gap to be filled
  silently: with no function symbols, unification is a total,
  decidable function on a finite term shape, the occurs check is
  trivial, and term size is bounded. A function-symbol extension is
  a separate, explicitly-scoped change, not a quiet widening.
- Lean core only, no Mathlib, no Batteries. Lean 4.12 core has NO
  `Finite`, `Fintype`, or `Rat` (verified by `#check` probe
  2026-10-28: all three are unknown identifiers in core).
  Therefore:
  - Finiteness is defined here as an explicit enumeration
    (`FiniteEnum`, see §5), not by appealing to a library class.
  - Rational weights are represented as scaled naturals:
    `Weight := Nat`, 1 unit = 0.001 nat of entropy. A rational
    weight `p/q` is represented exactly by scaling; all guard
    arithmetic is `Nat` arithmetic discharged by `omega`.
    A `Rat`-based guard is a future refinement, not a claim made here.
- Prolog control flow is DATA, never Lean control flow. The search
  stack is the `alternatives` field of `State` (see §3). The Lean
  recursion in the future `solve` is over `fuel : Nat` only; the
  backtracking stack it manipulates is data.

## 1. Syntax measures (LogosLab/Syntax.lean)

```lean
termSize   : Term -> Nat
termSize (Term.var _)   = 1
termSize (Term.const _) = 1

atomSize   : Atom -> Nat
atomSize a = a.args.length          -- each arg has size 1, so this is total term size

goalSize   : Goal -> Nat
goalSize (Goal.atom a) = atomSize a
goalSize Goal.cut       = 0

resolventSize : List Goal -> Nat
resolventSize gs = (gs.map goalSize).sum
```

These are size functions, not termination measures by themselves.
They are used inside `mu` (§4) and inside the future completeness
argument (branching is over `Program`, a finite `List Clause`).

## 2. Substitution / unification measures (LogosLab/Syntax.lean)

```lean
applySubst : Subst -> Term -> Term
-- Structural recursion on the substitution LIST, not on the term.
-- applySubst [] t = t
-- applySubst ((x, v) :: rest) (Term.var y) =
--     if y = x then applySubst rest v else applySubst rest (Term.var y)
-- applySubst ((x, v) :: rest) (Term.const c) = Term.const c
-- Termination: the list argument strictly shrinks at every call.
-- Invariant maintained by `bind` (see code): a new binding's term is
-- pre-applied with the old substitution, and new bindings are pushed
-- at the head, so head-first lookup follows chains in order.

bind : Subst -> Nat -> Term -> Subst
bind s x t = (x, applySubst s t) :: s
-- Phase 3 refactor: applySubst is now ORDER-INDEPENDENT (erase
-- version, see Syntax.lean): look up the first binding in the
-- whole list, then apply the substitution without that binding
-- to its value; measure is s.length, via erase_length_lt.
-- The Phase 1/2 order-dependent definition was unsound in a
-- deeper way than the Phase 2 bind-update patched: e.g.
-- [(1, const 42), (0, var 1)] applied to var 0 gave var 1,
-- not const 42, because a variable bound BEFORE the position
-- where its chain was encountered was never resolved. The
-- erase version gives const 42 for both orders (verified by
-- #eval, Phase 3), and push-only bind is sufficient with it:
-- a term going through an older binding mentioning the new
-- variable resolves that variable through the whole new
-- substitution, whose first binding for it is the new one.
-- The Phase 2 applyOne update is therefore removed.
-- `unify_sound` is still blocked, but for a sharper reason
-- than before (see STATUS.md Phase 3): bind preservation
-- needs an acyclicity / ranking invariant for unify-reachable
-- substitutions, not just effectively-unbound. Counterexample
-- for the naive statement: cyclic s = [(x, var y), (y, var x)],
-- bind x ↦ const 42, applied to var y: old gives var y,
-- new gives const 42, even though applySubst s (var x) = var x.
-- Unify never creates such a cycle (to bind y ↦ var x, the
-- applied terms would have to be var y vs var x, but under s
-- the applied term for var x is already var y), so the
-- invariant is about reachability, not about arbitrary s.
-- This does NOT block syntactic replay_sound / checker_sound,
-- which replay unify equations rather than asserting
-- applied-atom equality.

unifyTerm : Subst -> Term -> Term -> Option Subst
unifyArgs : Subst -> List Term -> List Term -> Option Subst
-- Structural recursion on the argument lists. Total: length mismatch
-- and constant mismatch return `none`, never a failure to terminate.
unifyAtom : Subst -> Atom -> Atom -> Option Subst
-- `none` unless predicates are equal; otherwise `unifyArgs` on args.
```

FUTURE lemma (blocked, see STATUS.md): `unify_sound` — if
`unifyAtom s a b = some s'` then `applySubst s' a = applySubst s' b`
as atoms (after applying `s'` to both argument lists). The missing
piece is an `applySubst`-composition lemma, stated precisely in
STATUS.md. It is NOT claimed here.

## 3. State and the Resolve transition system (LogosLab/State.lean)

```lean
structure Alternative where
  goals      : List Goal
  subst      : Subst
  depth      : Nat
  cutBarrier : Nat
  deriving DecidableEq, Repr

structure State where
  goals      : List Goal       -- resolvent stack
  subst      : Subst            -- triangular assoc-list
  depth      : Nat              -- depth counter
  cutBarrier : Nat              -- index into `alternatives`
  alternatives : List Alternative  -- explicit backtracking stack (DATA)
  abduced    : List Atom        -- hypotheses added so far (the Δ)
  deriving DecidableEq, Repr
```

```lean
step : Program -> State -> List State
-- step prog st enumerates ALL one-step successors of st, as data.
--   goals = []              -> []                        (terminal: no successors)
--   goals = Goal.cut :: rs  -> [{ st with goals := rs,
--                                  alternatives := st.alternatives.take st.cutBarrier }]
--   goals = Goal.atom a :: rs ->
--     for each clause c in prog (in order) with unifyAtom st.subst c.head a = some s',
--     one successor with goals := c.body ++ rs, subst := s', depth := st.depth + 1,
--     cutBarrier := st.alternatives.length,
--     alternatives := st.alternatives ++ (the remaining clause choices,
--                       each recorded with cutBarrier := st.alternatives.length)
-- Non-determinism lives ONLY in this enumerated list. `step` itself is
-- a total function: same (prog, st) always gives the same list.

Resolve : Program -> State -> State -> Prop
Resolve prog st st' := st' ∈ step prog st
```

Determinism theorem (proved in this phase, `State.lean`):

```lean
step_deterministic : ∀ (prog : Program) (st : State),
  step prog st = step prog st
```

This is function determinism, stated honestly: it says the
enumeration is a function, not that search has one outcome. Search
non-determinism is the list `step prog st` itself.

Cut lemma (proved in this phase, `State.lean`):

```lean
cut_lemma : ∀ (st : State) (rs : List Goal),
  let st' := (step prog { st with goals := Goal.cut :: rs })[0]  -- the unique Cut successor
  st'.alternatives = st.alternatives.take st.cutBarrier
  ∧ st'.goals = rs
  ∧ (∀ a ∈ st'.alternatives, a ∈ st.alternatives)
  ∧ st'.alternatives ++ st.alternatives.drop st.cutBarrier = st.alternatives
```

In words: cut discards exactly the alternatives after the barrier
and preserves exactly those before it. The actual proved statement
in code is phrased over `cutState` (the Cut successor constructor)
so it does not depend on list-indexing; see `State.lean`.
Scope note: the barrier recorded at clause entry is
`st.alternatives.length` at expansion time (see `step` above).
Full ISO predicate-invocation bookkeeping — i.e. proving that the
barrier recorded by `step` is exactly the barrier ISO cut assigns
to the invoking goal — is a solver-phase lemma, listed as blocked
in STATUS.md, not smuggled into this lemma.

## 4. Termination measures (Phase 2: solver code now exists)

Phase 1 stated these signatures; Phase 2 implements them in
`LogosLab/Deriv.lean`, with the exact signatures below (plus the
abducible list and guard parameters, which Phase 1's sketch omitted
and which are now fixed):

```lean
-- Primary measure: fuel, structural recursion on Nat.
solve : (fuel : Nat) -> Program -> List Atom -> Guard -> State -> List Answer
-- Every recursive call is on `fuel` in the `fuel + 1` pattern,
-- i.e. visibly `fuel - 1` in effect, never on the same fuel.
-- No `partial`, no `unsafeRec`. Guards are evaluated at every node
-- BEFORE recursion: a node with guard = false returns [].

-- Answer type (Phase 2, as sketched in Phase 1):
--   structure Answer where
--     abduced : List Atom
--     subst   : Subst

solve_terminates : ∀ (fuel : Nat) (prog : Program) (A : List Atom)
    (guard : Guard) (st : State),
  fuel = 0 -> solve fuel prog A guard st = []
-- PROVED in Phase 2 (Replay.lean), by definition of `solve` on
-- fuel = 0. Axioms: [propext] (allowed, from standard lemmas).

-- Cut propagation limitation (Phase 2, honest): `solve` uses
-- `step` successors and `cutStep` for cut goals, so a cut
-- truncates the current state's alternatives field, but that
-- truncation is NOT yet propagated to the parent's successor
-- list. This affects completeness (answers that should be pruned
-- may still be enumerated), not soundness (every returned answer
-- still has a Deriv, proved). Full ISO cut propagation needs a
-- stack-based solver and is listed as blocked in STATUS.md.

-- Abductive deepening measure:
mu : List Atom -> Nat
mu Δ = Δ.length + (Δ.map atomSize).sum
-- mu(explanation) = number of abducible literals + total term size,
-- exactly as specified. Since atomSize = args.length here, this is
-- Δ.length + total argument count.

remainingBudget : Nat -> Nat   -- the hypothesis-count budget left
extendBudget : Nat -> Nat
extendBudget b = b - 1
extendBudget_lt : ∀ b, b ≠ 0 -> extendBudget b < b
-- Proved in this phase (Measures.lean) by cases on the budget. The abductive
-- extension rule in the solver phase may only fire when the new
-- hypothesis count is within budget AND the remaining budget strictly
-- decreases; that rule is future code, not present code.

alp_loop : Observation -> Nat -> List Answer   -- FUTURE, signature only
alp_loop_terminates : ∀ (obs : Observation) (depth : Nat),
  ∃ n, alp_loop obs depth = alp_loop obs (depth + n)
-- Statement as specified, with `Observation` to be fixed in solver
-- phase (provisionally: a goal atom, i.e. `Atom`). BLOCKED until
-- `alp_loop` exists; the missing piece is the loop definition itself,
-- not a proof trick. See STATUS.md.
```

RelHom note: no `WellFoundedRecursion` / `RelHom` is needed for the
primary solver measure, because recursion is structural on `fuel`.
If a future refinement replaces fuel by a well-founded measure, it
MUST declare its relation and RelHom in this file BEFORE that code
lands, and this file must be updated first. Do not add well-founded
recursion silently.

## 5. Finiteness by construction (LogosLab/Finite.lean)

Abducibles are NOT an open predicate. The abducible set is a finite
list, given as data:

```lean
-- AbducibleSet: a List Atom, carried as data wherever explanations are built.
-- An explanation Δ is a List Atom with Δ ⊆ abducibles and Δ.length ≤ depth.

FiniteEnum (α : Type) : Prop
FiniteEnum α := ∃ l : List α, ∀ a : α, a ∈ l
-- An explicit enumeration list. This is the finiteness notion used in
-- this project, because Lean core has no Finite/Fintype class.

allFin : (k : Nat) -> List (Fin k)
-- allFin k enumerates every Fin k, in order. Defined by recursion on k.

boundedLists : (k d : Nat) -> List (List (Fin k))
-- boundedLists k d enumerates every List (Fin k) of length ≤ d.
-- Defined by recursion on d, extending the previous level by every Fin k.
-- An explanation over k abducibles with hypothesis count ≤ d is encoded
-- as a List (Fin k) (indices into the abducible list); boundedLists is
-- its enumeration.

Finite (explanations obs depth)   -- REQUIRED theorem, FUTURE
-- Precise form (future): for a fixed abducible list A (length k) and
-- depth d, FiniteEnum { Δ : List Atom // Δ ⊆ A ∧ Δ.length ≤ d },
-- proved by exhibiting the injection Δ ↦ indices of Δ in A and the
-- enumeration boundedLists k d.
-- BLOCKED in Phase 1: the injection + membership proof is not written.
-- The enumeration function exists; the theorem does not yet. See STATUS.md.
-- No appeal to "constraints keep it small" is made anywhere.
```

## 6. Guards (LogosLab/Guards.lean)

```lean
Guard : Type
Guard = State -> Bool
-- A guard is evaluated at every extension node BEFORE recursion, inside
-- (future) solve. Pruning happens inside solve, never outside it.

weight : Atom -> Nat   -- scaled entropy/weight, 1 unit = 0.001 nat
explanationWeight : List Atom -> Nat
explanationWeight Δ = (Δ.map weight).sum

weightGuard : (T : Nat) -> Guard
weightGuard T st = (explanationWeight st.abduced ≤ T)   -- Bool via Nat.decLe
-- Lower bound on remaining goals is 0 (weights are non-negative), so
-- running weight + 0 ≤ T is the guard. A non-trivial admissible lower
-- bound is a future refinement; the soundness argument for THIS guard
-- is monotonicity of weight under extension (weights ≥ 0), which is
-- the lemma listed as blocked in STATUS.md.

prune_sound : ∀ (st : State), guard st = false ->
  ∀ ans ∈ solve (extend st), ¬ ValidExplanation ans
-- REQUIRED theorem, FUTURE. `extend` and `ValidExplanation` do not exist
-- yet (they belong to the solver phase), so this is a signature in this
-- file, not a proved theorem. The guard-soundness argument that must be
-- supplied for weightGuard: extension only adds non-negative weight,
-- so a state already over T can never extend to a valid (≤ T)
-- explanation. For the SEND+MORE=MONEY guard, the argument is column
-- necessity (see below).

-- SEND+MORE=MONEY guard (executable witness, Guards.lean):
type Letter := Nat   -- letter codes: S,E,N,D,M,O,R,Y as distinct Nats
Assignment := List (Nat × Nat)   -- (letter, digit), digits 0..9
sendMoreMoneyGuard : Assignment -> Bool
-- Checks, on a PARTIAL assignment, only what is already forced:
--   * no letter gets two different digits, no digit is reused
--     (injective on assigned letters);
--   * every fully-assigned column equation holds, with carry computed
--     exactly from the column to its right (units: D+E=Y+10*c1,
--     tens: N+R+c1=E+10*c2, hundreds: E+O+c2=N+10*c3,
--     thousands: S+M+c3=O+10*c4, with c4 = M and M ≠ 0, S ≠ 0 as
--     leading-zero conditions when those letters are assigned).
-- A column whose letters are not all assigned is NOT checked (it cannot
-- yet fail). Hence the guard is a necessary condition: any full solution
-- passes every partial check. Proving that necessity is the blocked lemma
-- `sendMoreMoneyGuard_necessary` in STATUS.md; the function itself is
-- executable in this phase and is #eval-tested in Guards.lean's examples
-- (see code comments there — examples are data, not solver runs).
```

## 7. Lemma-dependency graph

Phase 1 (proved, in code):

```
termSize / atomSize / goalSize
  └─ mu (Measures.lean, definition)
applySubst (structural on Subst)
  └─ bind ── unifyTerm ── unifyArgs ── unifyAtom
step (Program, State) ── Resolve (membership in step)
  ├─ step_deterministic  (rfl: step is a function)
  └─ cut_lemma           (List.take_append_drop + List.mem_of_mem_take)
extendBudget_lt (omega)
cutState definition ── cut_lemma
weightGuard / explanationWeight (definitions)
sendMoreMoneyGuard (definition, executable)
allFin / boundedLists (definitions, enumeration)
```

Future (blocked, in dependency order — each needs the one above it):

```
unify_sound
  └─ applySubst composition lemma (applySubst (bind s x t) = ...)
      └─ replay_sound (solve answers have Deriv)
          └─ checker_sound (kernel replays external candidates)
completeness_bounded
  ├─ finite branching: Program is a List Clause (finite by data)
  ├─ unifyAtom total (done: it is a total function)
  └─ bounded enumeration (boundedLists + index injection)
minimality
  └─ decidable subsumption check + filtering pass (not written)
prune_sound (weight + SEND+MORE=MONEY)
  ├─ weight monotonicity under extension
  └─ sendMoreMoneyGuard_necessary
finiteness theorem
  └─ index injection + boundedLists membership
solve_terminates / alp_loop_terminates
  └─ solve / alp_loop definitions (not written, by design in Phase 1)
```

## 8. What Phase 1 deliberately did NOT contain (now Phase 2)

Phase 1 contained no `solve`, no `alp_loop`, no `Deriv`, no
`checker`, no `Answer`, and no `#eval` pipeline run — claiming
any of those then would have been fabrication.

Phase 2 (2026-10-28) DOES contain: `Deriv`, `Answer`, `solve`,
`checker` (trace replay), `replay_sound`, `checker_sound`,
`replayTrace_sound`, `solve_terminates`, and the burglary/alarm
`#eval` pipeline in `Root.lean` (T = 3: [burglary], [earthquake];
T = 2: [earthquake] only).

Still NOT contained, honestly: no `alp_loop`, no theorems 3–6,
no `unify_sound`, no full ISO cut propagation, no finiteness
theorem. See STATUS.md Phase 2 for the precise blockers.
No `sorry`, `admit`, `axiom` declaration, `unsafe`, `partial`,
or `native_decide` in any phase. Grep verification is in
STATUS.md.
