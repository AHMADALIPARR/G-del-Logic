# STATUS.md — logos-lab, Phase 1 + Phase 2 + Phase 3 (2026-10-28)

## Phase 3, part 1 — begun (user said "Ok begin", 2026-10-28 12:30 PDT)

Refactor first, because the Phase 2 statement of `unify_sound`
was unprovable for a deeper reason than the bind-update patched:
the old `applySubst` was order-dependent. Part 1, verified by
clean `lake build`:

- `applySubst` is now erase-based and order-independent
  (`LogosLab/Syntax.lean`): first binding in the whole list,
  then apply the substitution without that binding to its value;
  termination by `s.length` via `erase_length_lt` (proved,
  [propext]). Example verified by #eval: [(1, const 42),
  (0, var 1)] applied to var 0 now gives const 42, not var 1.
- `bind` is back to push-only (Phase 2 `applyOne` update removed);
  with whole-subst lookup, push-only is sufficient, and it
  simplifies the preservation proof. Old Phase 2 counterexample
  (bind x ↦ var y, then y ↦ const 42, applied to var x) still
  gives const 42 on both sides.
- All Phase 1/2 theorems still compile (only axiom change:
  `step_deterministic` / `step_cut` now [propext], from the
  well-founded `applySubst`); burglary #eval unchanged.
- New proved lemmas in `LogosLab/Unify.lean` ([propext] each):
  `lookup_bind`, `erase_bind_self`, `erase_bind_ne`,
  `applySubst_const`, `applySubst_nil`,
  `applySubst_var_unbound`. Because the new `applySubst` is
  well-founded and irreducible, these are proved via its
  equation lemmas (`applySubst.eq_1/eq_2/eq_3`), not by `rfl`.

Still open, precisely: bind preservation and `unify_sound`
need an acyclicity / ranking invariant for unify-reachable
substitutions. Naive preservation is FALSE for cyclic s
(counterexample in MEASURES.md §2: s = [(x, var y),
(y, var x)], bind x ↦ const 42, var y: old var y, new
const 42, even though applySubst s (var x) = var x). Unify
never creates such a cycle, so the next step is to define
that invariant (e.g. a ranking rank : Nat -> Nat with
lookup z = var w → rank w < rank z for first bindings,
preserved by unify binds) and prove preservation under it,
then unifyTerm / unifyArgs / unifyAtom soundness by induction.
Stack-based solver for full ISO cut propagation is AFTER
`unify_sound`, not in this part.

## Phase 2 — what changed (user said "Go", 2026-10-28 12:07 PDT)

Phase 2 implements, in order from the Phase 1 next-phase list:
`Deriv` + `solve` + kernel `checker`, then `replay_sound` and
`checker_sound`. Clean `lake build` verified 2026-10-28, including
the burglary/alarm `#eval` pipeline in `Root.lean`.

### Phase 2 proved theorems (Root.lean #print axioms)

| Theorem | Statement (short) | Axioms |
|---|---|---|
| `replay_sound` (Thm 1) | ans ∈ solve fuel … st → Deriv for st.goals/subst/abduced to ans | [propext, Quot.sound] — both allowed; from standard lemmas, not an assumed axiom declaration |
| `checker_sound` (Thm 2) | checker = true → Deriv for the candidate | [propext] |
| `replayTrace_sound` | replayTrace = some (Δf, sf) → Deriv with those finals | [propext] |
| `solve_terminates` | fuel = 0 → solve = [] | [propext] |

No `sorryAx`, no `Classical.choice` in any of these. Soundness
here is SYNTACTIC: a derivation is built by following the exact
steps the solver / trace took, using the unify equations those
steps already produced. It does not claim `unify_sound` (see
blocked below); conflating the two would be proof-stamping.

### Phase 2 #eval pipeline (Root.lean, burglary/alarm, guard active)

- T = 3: `[{abduced := [burglary]}, {abduced := [earthquake]}]`
- T = 2: `[{abduced := [earthquake]}]` (burglary, weight 3, pruned)

### Phase 2 bug found and fixed (not hidden)

Phase 1 `bind` (push only, no update) was UNSOUND for chains.
Counterexample, verified by #eval: bind x ↦ var y, then bind
y ↦ const 42, applied to var x gave var 1-equivalent (var y)
instead of const 42. Fixed `bind` now updates existing bindings'
values by the new binding (`applyOne`), and the counterexample
now evaluates to const 42 on both sides, and the corresponding
`unifyArgs` case gives equal applied terms. The fix is in
`LogosLab/Syntax.lean` and documented in MEASURES.md §2.

### Phase 2 limitations, stated plainly

- Cut propagation in `solve` is incomplete: a cut truncates the
  current state's alternatives field via `cutStep`, but that
  truncation is not yet propagated to the parent's successor list
  in `solve`'s list recursion. This affects completeness, not
  soundness (every returned answer still has a Deriv). Full ISO
  cut propagation needs a stack-based solver; it is blocked under
  completeness below, not claimed.
- `unify_sound` remains blocked (see below). It is a semantic
  lemma, separate from syntactic replay/checker soundness.

## What Phase 1 is

MEASURES.md first, then the state-space definitions, exactly as the
brief's opening instruction requires: measures stated before code,
Resolve as an explicit transition system, no solver code yet.

Local only: `~/workspace/logos-lab`, git, NO remote, NOT pushed.
The URL `https://github.com/AHMADALIPARR/logos-lab` was given in the
brief, but no repo name confirmation plus fresh token for a push was
given in this turn, so nothing was created or pushed remotely, per
standing push rules. A push, if wanted, needs the destination named
again plus a fresh single-use token.

## Build (verified 2026-10-28)

```
cd ~/workspace/logos-lab && lake build
Build completed successfully.
```

Toolchain (exact pins):
- `lean-toolchain`: `leanprover/lean4:v4.12.0`
- `lakefile.lean`: package `logosLab` v0.1.0, Lean core only,
  NO external dependencies. See MEASURES.md §0 for why: Lean 4.12
  core has no `Finite`, `Fintype`, or `Rat` (verified by `#check`
  probe), so finiteness and weights are defined in-project.

Guard witnesses (executable, in `LogosLab/Guards.lean`, printed on build):
- `sendMoreMoneyGuard sendMoreMoneySolution = true`
  (S=9, E=5, N=6, D=7, M=1, O=0, R=8, Y=2)
- `sendMoreMoneyGuard sendMoreMoneyBadPartial = false`
  (D=1, E=2 forces Y=3, not 9)

## SELF-CHECK PROTOCOL — Phase 1

### Proved theorems (in code, with #print axioms in Root.lean)

| Theorem | Statement (short) | Axioms per #print axioms | File / line dependency |
|---|---|---|---|
| `cut_lemma` | Cut successor's alternatives = take barrier; goals = tail; survivors ⊆ originals; survivors ++ dropped = original | none | `LogosLab/State.lean`, via `cutStep` and `List.take_append_drop` |
| `step_deterministic` | `step prog st = step prog st` (function determinism; search non-determinism is the enumerated list) | none | `LogosLab/State.lean`, `step` definition |
| `step_cut` | `step` on a Cut head = `[cutStep st rs]` | none | `LogosLab/State.lean`, `step` definition |
| `extendBudget_lt` | `b ≠ 0 -> extendBudget b < b` | `[propext]` — allowed, and it arises from `simp`, not from an assumed axiom declaration | `LogosLab/Measures.lean`, cases on budget |
| `mu_empty` | `mu [] = 0` | none | `LogosLab/Measures.lean`, `mu` definition |

### Required theorems 1–6 — status (updated Phase 2)

Phase 1: none of theorems 1–6 was proved, by design (subjects did
not exist yet). Phase 2: theorems 1 (`replay_sound`) and 2
(`checker_sound`) ARE proved, syntactically (see Phase 2 table
above), plus `solve_terminates`. Theorems 3–6 remain blocked, as
listed below, not downgraded, not silently renamed. `unify_sound`
(semantic) is a separate lemma, also still blocked — it is NOT
the same as syntactic replay soundness, and Phase 2 does not
claim it.

### Forbidden patterns — grep verification

Run in the repo root (excluding `.lake/` build output):

```
grep -rnE 'sorry|admit|axiom|unsafe|partial|native_decide' --include='*.lean' .
```

Result 2026-10-28: NO actual forbidden declarations. The only
matches are false positives:
- the word "partial" inside comments about partial assignments
  (`Guards.lean`), which is data terminology, not Lean `partial`;
- the string "axioms" inside the required `#print axioms` commands
  in `Root.lean` themselves.
- No `sorry`, no `admit`, no `axiom` declaration, no `unsafe`,
  no `native_decide` anywhere in source.
- One `simp [extendBudget]` (term-mode, in `extendBudget_lt`,
  after `cases` on the budget) — not a `by simp` chain closing a
  goal by accident, and its result is kernel-checked by the build.

No placeholder `by simp` chains, no unported meta-programming
bypassing the kernel, no "finite because constraints" claim:
finiteness is an explicit enumeration function (`boundedLists`),
and its theorem is blocked below until the injection is proved.

### #eval pipeline

Phase 1: ABSENT, deliberately (no solver yet). Phase 2: PRESENT
in `Root.lean` — burglary/alarm with entropy guard active, T = 3
gives [burglary], [earthquake]; T = 2 gives [earthquake] only.
See Phase 2 table above.

## BLOCKED — precise missing lemmas (do not downgrade)

1. `replay_sound` — PROVED in Phase 2, syntactically (see table
   above). The separate semantic lemma below is NOT proved:
   `unify_sound`:
   `∀ s a b s', unifyAtom s a b = some s' -> applySubstAtom s' a = applySubstAtom s' b`.
   Blocker, precisely (Phase 3, sharper): the naive
   bind-preservation lemma is FALSE even under the
   effectively-unbound hypothesis. Counterexample: cyclic
   s = [(x, var y), (y, var x)], bind x ↦ const 42, u = var y:
   old application gives var y, new gives const 42, even
   though applySubst s (var x) = var x. An earlier
   counterexample (s = [(a, var x), (x, const 1)], bind
   x ↦ var b, u = var a: new var b, old const 1) already
   showed the hypothesis is needed; the cycle example shows
   it is not sufficient. The correct statement needs an
   acyclicity / ranking invariant for unify-reachable
   substitutions (see Phase 3 part 1 above). That proof is
   still open, and is the next step before the stack solver.

2. `checker_sound` — PROVED in Phase 2, syntactically, via
   `replayTrace_sound` (see table above).

3. `completeness_bounded` — BLOCKED, on the bounded-enumeration
   membership lemma:
   `∀ k d l, l.length ≤ d -> l ∈ boundedLists k d`,
   and on full ISO cut propagation in `solve` (Phase 2 limitation
   above: cut truncates the current state's alternatives, but
   that truncation is not yet propagated to the parent's
   successor list, so a stack-based solver is needed for the
   completeness argument). Finite branching itself is already by
   data (`Program` is a list) and `unifyAtom` is already a total
   function; those two pieces are done, the enumeration
   membership proof and cut propagation are not.

4. `minimality` — BLOCKED on the decidable subsumption check and
   the filtering pass not existing. Missing lemma, precisely:
   a function `subsume : List Atom -> List Atom -> Bool` with
   `subsume Δ1 Δ2 = true <-> Δ1 ⊆ Δ2` (on abducible lists), plus
   a filter whose output provably contains no pair Δ1 ⊂ Δ2.

5. `prune_sound` and finiteness — BLOCKED.
   - Weight guard: missing `weight_mono_extend`:
     `explanationWeight w (Δ ++ [a]) = explanationWeight w Δ + w a`
     (and hence ≥), from which over-threshold states can never
     extend to a ≤ T explanation.
   - SEND+MORE=MONEY guard: missing `sendMoreMoneyGuard_necessary`:
     every full solution (as an assignment) passes
     `sendMoreMoneyGuard` on every partial sub-assignment of it.
   - Finiteness: missing the index injection:
     for a fixed abducible list A of length k, an injective map
     from `{ Δ // Δ ⊆ A ∧ Δ.length ≤ d }` to `List (Fin k)`
     (indices in A), combined with the boundedLists membership
     lemma in (3).

6. `cut_lemma` (full ISO form) — PARTIAL. The data-level lemma in
   `State.lean` IS proved (see table above). What remains blocked
   is the solver-phase lemma that the barrier recorded by `step`
   (`st.alternatives.length` at expansion time) is exactly the
   barrier ISO cut assigns to the invoking goal. That statement
   needs the solver's goal-invocation bookkeeping, which does not
   exist yet.

7. `solve_terminates` — PROVED in Phase 2, by definition of
   `solve` on fuel = 0 (see table above).

8. `alp_loop_terminates` — BLOCKED on `alp_loop` and `Observation`
   not existing. Statement fixed in MEASURES.md §4; the loop
   definition itself is the missing piece, not a proof trick.

## Next phase (Phase 3, in order)

1. `unify_sound` under the effectively-unbound hypothesis
   (see blocked item 1 above for the precise statement).
2. Stack-based `solve` with full ISO cut propagation, then
   `completeness_bounded` (bounded enumeration membership +
   index injection for finiteness).
3. Subsumption check + filter (`minimality`), guard necessity
   lemmas (`prune_sound`), full ISO cut lemma.
4. `alp_loop` + `alp_loop_terminates`, then a push decision
   (named destination + fresh token, or local only).
