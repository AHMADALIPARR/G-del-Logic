/-
  LogosLab.Syntax — deep embedding of a Datalog-style Horn fragment.

  Terms are Var Nat | Const Nat only: no function symbols.
  See MEASURES.md §0-§2 for why, and for the measure definitions
  that this file implements. No solver code lives here: only syntax,
  substitution, and total unification.
-/

namespace LogosLab

/-- A term: a variable (de Bruijn-style index into the substitution,
    not a binder) or a constant code. No function symbols. -/
inductive Term where
  | var : Nat -> Term
  | const : Nat -> Term
deriving DecidableEq, Repr, Inhabited

/-- An atom: a predicate code plus a list of terms. -/
structure Atom where
  pred : String
  args : List Term
deriving DecidableEq, Repr, Inhabited

/-- A goal: an atom to prove, or the cut marker `!`. -/
inductive Goal where
  | atom : Atom -> Goal
  | cut : Goal
deriving DecidableEq, Repr, Inhabited

/-- A Horn clause: head :- body. An empty body is a fact. -/
structure Clause where
  head : Atom
  body : List Goal
deriving DecidableEq, Repr, Inhabited

/-- A program is a finite list of clauses, in order. Finiteness of
    branching is by data: the program list itself. -/
abbrev Program := List Clause

/-- A triangular substitution: an association list, newest binding
    first. See `applySubst` for the lookup discipline. -/
abbrev Subst := List (Nat × Term)

/-- Size of a term. Every term has size 1 in this fragment. -/
def termSize : Term -> Nat
  | Term.var _ => 1
  | Term.const _ => 1

/-- Size of an atom: its total term size, i.e. its argument count. -/
def atomSize (a : Atom) : Nat :=
  a.args.length

/-- Size of a goal: cut contributes 0. -/
def goalSize : Goal -> Nat
  | Goal.atom a => atomSize a
  | Goal.cut => 0

/-- Size of a resolvent: sum of goal sizes. -/
def resolventSize (gs : List Goal) : Nat :=
  (gs.map goalSize).foldr (· + ·) 0

/-- Look up the first binding for a variable, if any. -/
def lookupSubst : Subst -> Nat -> Option Term
  | [], _ => none
  | (x, v) :: rest, y => if y = x then some v else lookupSubst rest y

/-- Erase the first binding for a variable, if any. -/
def eraseSubst : Subst -> Nat -> Subst
  | [], _ => []
  | (x, v) :: rest, y => if y = x then rest else (x, v) :: eraseSubst rest y

/-- Erasing a bound variable strictly shortens the substitution.
    This is the termination argument for `applySubst` below. -/
theorem erase_length_lt (s : Subst) (y : Nat) (v : Term)
    (h : lookupSubst s y = some v) :
    (eraseSubst s y).length < s.length := by
  induction s generalizing y with
  | nil => simp [lookupSubst] at h
  | cons head rest ih =>
      obtain ⟨x, w⟩ := head
      simp only [lookupSubst] at h
      by_cases hx : y = x
      · simp [hx, eraseSubst]
      · have h2 : lookupSubst rest y = some v := by simpa [hx] using h
        have hlt := ih y h2
        simp [hx, eraseSubst, hlt]

/-- Apply a substitution to a term. Phase 3 refactor (see
    MEASURES.md §2): the Phase 1/2 definition was ORDER-DEPENDENT
    — a variable bound BEFORE the position where its chain was
    encountered was not resolved (e.g. [(1, const 42),
    (0, var 1)] applied to var 0 gave var 1, not const 42).
    This definition is order-independent: look up the FIRST
    binding for the variable in the WHOLE list, then apply the
    substitution WITHOUT that binding to its value. Removing the
    bound variable breaks cycles (a cycle collapses to its
    starting variable instead of looping), and the measure is
    `s.length`, strictly decreasing by `erase_length_lt`.
    First binding wins, so a new binding pushed at the head
    correctly shadows older bindings for the same variable. -/
def applySubst : Subst -> Term -> Term
  | [], t => t
  | _s, Term.const c => Term.const c
  | s, Term.var y =>
      match h : lookupSubst s y with
      | none => Term.var y
      | some v => applySubst (eraseSubst s y) v
termination_by s _ => s.length
decreasing_by exact erase_length_lt _ _ _ h

/-- Bind a variable, pre-applying the old substitution to the value
    and pushing the new binding at the head. Phase 3: with the
    order-independent `applySubst` above, push-only is sufficient
    — a term that goes through an older binding mentioning the
    newly bound variable will resolve that variable through the
    whole new substitution, whose first binding for it is the new
    one. The Phase 2 `applyOne` update is therefore removed; it
    was a patch for the order-dependent definition, not a
    semantic requirement, and keeping it would complicate the
    bind-preservation proof for no benefit. -/
def bind (s : Subst) (x : Nat) (t : Term) : Subst :=
  (x, applySubst s t) :: s

/-- Apply a substitution to every argument of an atom. -/
def applySubstAtom (s : Subst) (a : Atom) : Atom :=
  { pred := a.pred, args := a.args.map (applySubst s) }

/-- Unify two terms under a substitution. Total: returns `none` on
    constant mismatch, `some` otherwise. -/
def unifyTerm (s : Subst) (t1 t2 : Term) : Option Subst :=
  match applySubst s t1, applySubst s t2 with
  | Term.var x, Term.var y =>
      if x = y then some s else some (bind s x (Term.var y))
  | Term.var x, Term.const c => some (bind s x (Term.const c))
  | Term.const c, Term.var x => some (bind s x (Term.const c))
  | Term.const a, Term.const b =>
      if a = b then some s else none

/-- Unify two argument lists pairwise. Total: length mismatch and
    any pairwise failure return `none`. Structural recursion on
    the argument lists. -/
def unifyArgs : Subst -> List Term -> List Term -> Option Subst
  | s, [], [] => some s
  | s, t1 :: r1, t2 :: r2 =>
      match unifyTerm s t1 t2 with
      | some s' => unifyArgs s' r1 r2
      | none => none
  | _s, _, _ => none

/-- Unify two atoms: predicates must be equal, then unify arguments. -/
def unifyAtom (s : Subst) (a b : Atom) : Option Subst :=
  if a.pred = b.pred then unifyArgs s a.args b.args else none

end LogosLab
