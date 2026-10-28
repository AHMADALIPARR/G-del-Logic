# How it works

A longer walk through the two projects in this repo. The figures are in `docs/img/`.

## Part 1: the Gödel Machine (`godel-machine/GodelMachine.lean`)

The file is built in six layers, each one resting on the one before.

**Layer 0, pairing.** `pair a b = 2^a × (2b + 1)` turns two numbers into one. The exponent of 2 is the first number, the odd part is the second. It is a one-to-one match with the positive numbers, and the file proves both directions (`unpair_pair`, `pair_unpair`).

**Layer 1, syntax.** The engine's own language (terms, goals, rules) is written as ordinary Lean data types. Each one has an `encode` and a `decode`, built from the pairing, and a theorem that decoding an encoded value gives the value back. A whole program is a list of rules, coded the same way, so a program is one number.

**Layer 2, running a program.** A program is run by closing it: start from a seed fact, apply every rule whose body is already known, and repeat. The set of facts that can ever show up is bounded by the atoms the program mentions, so the loop reaches a fixed point after a bounded number of rounds. The run ends because of how it is built, not because anyone promised it would.

**Layer 3, what counts as better.** A program `P'` improves on `P` when three things hold: the outputs are the same, `P'` has fewer rules, and the cost (the gap between all atoms the program mentions and the atoms it actually derives) did not go up.

**Layer 4, the gate.** `install P g` decodes the number `g` into a candidate. It then searches for a proof object: a rule index, a body goal in that rule that is never derived, and the fact that the candidate is `P` with that rule removed. Only a candidate that comes with such a proof is returned. `install_improves` shows that whatever comes out is an improvement in the sense of layer 3.

**Layer 5, the loop.** `improve` feeds a list of candidate numbers through the gate. A rejected candidate changes nothing. `improve_never_regresses` says the result is never longer than the start and always has the same outputs.

The one rewrite known today, dead-clause elimination, is the only way a program can change. To teach the machine another rewrite, add a case to the proof object and to the theorem that turns it into an improvement.

## Part 2: logos-lab

`logos-lab/` is a separate project on Lean 4.12.0. Its design starts from `MEASURES.md`, which states what gets measured (sizes, fuel, weights) before any code uses it.

**Syntax.** Terms are variables or constants. Atoms are a predicate name with a list of terms. A goal is an atom or the cut mark. A clause is a head with a body, and a program is a list of clauses. Bindings are kept as a list, newest first, and applying them to a term follows a variable through its chain until it reaches a constant or an unbound variable.

**Unify.** Two atoms unify if the predicates match and their arguments can be made equal, one pair at a time. A constant clash fails. A variable against anything adds a binding. `Unify.lean` holds the small lemmas about how bindings are looked up and erased.

**State.** One search state carries the goals left, the bindings, a depth, the cut barrier, the list of saved alternatives, and the hypotheses assumed so far. Because backtracking is just that list, the search is plain data a theorem can talk about.

**Resolve.** `step` takes a state and returns every successor. An empty goal list has none. A cut gives exactly one: the same state with the alternatives trimmed back to the barrier. An atom gives one successor per clause whose head unifies, in program order.

**Guards and finiteness.** A guard is a yes/no test on a state. The weight guard keeps the running total of hypothesis weights at or under a limit. Weights are whole numbers, one unit being a thousandth of a nat of entropy. The hypotheses an explanation may use come from a fixed list, and `Finite.lean` lists every possible explanation of a given size.

**Solve.** `solve` takes fuel, a program, the list of allowed hypotheses, a guard and a start state. At each node it checks the guard first. An empty goal list is an answer. A cut moves on. An atom tries every matching clause, and then, if the atom is one of the allowed hypotheses, assumes it. Each recursive call spends one unit of fuel.

**Derivations and the checker.** `Deriv` is a proof tree with one rule for each kind of move: nothing left to do, cut, resolve with a clause, assume a hypothesis. `replay_sound` shows every answer from `solve` has such a tree. A trace is a list of moves (`resolve i`, `abduce atom`, `cut`). `replayTrace` follows it and gives back the final hypotheses and bindings, and `checker` accepts a candidate answer only if its trace replays to exactly that answer. `checker_sound` shows that acceptance means a derivation exists.

**The example.** `Root.lean` runs the burglary and alarm program with the weight guard on. With a limit of 3 it returns both explanations. With a limit of 2 the burglary branch is cut and only the earthquake is returned.

The state of the proofs, and what is planned, is in [`../logos-lab/STATUS.md`](../logos-lab/STATUS.md).
