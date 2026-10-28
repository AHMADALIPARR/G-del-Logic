-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
/-
  LogosLab.Unify — substitution lemmas for `unify_sound`, Phase 3.

  The Phase 3 refactor changed `applySubst` to an order-independent
  erase-based definition (see Syntax.lean). Because that definition
  uses well-founded recursion, it is marked irreducible: simple
  facts about it are proved via its equation lemmas
  (`applySubst.eq_1/eq_2/eq_3`), not by `rfl` or plain `simp`.

  What is proved here: lookup/erase behaviour of `bind`, and
  `applySubst` on constants, on the empty substitution, and on
  unbound variables. What is NOT proved here yet: bind
  preservation and `unify_sound` itself. Those need an acyclicity
  invariant for the substitution (see STATUS.md Phase 3): the
  naive bind-preservation statement is false for cyclic
  substitutions, e.g. s = [(x, var y), (y, var x)] with bind
  x ↦ const 42, applied to var y (old: var y, new: const 42),
  even though applySubst s (var x) = var x. Unify-built
  substitutions never create such a cycle (to bind y ↦ var x,
  the applied terms would have to be var y vs var x, but under
  s the applied term for var x is already var y), so the
  remaining proof must carry an acyclicity / ranking invariant
  for unify-reachable substitutions, not just the
  effectively-unbound hypothesis. That invariant is the precise
  next step, not a vague "composition lemma".
-/

import LogosLab.Syntax

namespace LogosLab

/-- Lookup in a bound substitution: the new binding wins for its
    own variable, otherwise lookup is unchanged. -/
theorem lookup_bind (s : Subst) (x y : Nat) (t : Term) :
    lookupSubst (bind s x t) y =
      if y = x then some (applySubst s t) else lookupSubst s y := by
  simp only [bind, lookupSubst]

/-- Erasing the newly bound variable from a bound substitution
    recovers the old substitution. -/
theorem erase_bind_self (s : Subst) (x : Nat) (t : Term) :
    eraseSubst (bind s x t) x = s := by
  simp [bind, eraseSubst]

/-- Erasing a different variable keeps the new binding at the head. -/
theorem erase_bind_ne (s : Subst) (x y : Nat) (t : Term) (h : y ≠ x) :
    eraseSubst (bind s x t) y = (x, applySubst s t) :: eraseSubst s y := by
  simp [bind, eraseSubst, h]

/-- Applying any substitution to a constant leaves it unchanged. -/
theorem applySubst_const (s : Subst) (c : Nat) :
    applySubst s (Term.const c) = Term.const c := by
  cases s with
  | nil => rw [applySubst.eq_1]
  | cons _ _ => rw [applySubst.eq_2]; intro hc; cases hc

/-- The empty substitution is the identity. -/
theorem applySubst_nil (t : Term) : applySubst [] t = t := by
  rw [applySubst.eq_1]

/-- A variable with no binding in the substitution is unchanged. -/
theorem applySubst_var_unbound (s : Subst) (y : Nat)
    (h : lookupSubst s y = none) :
    applySubst s (Term.var y) = Term.var y := by
  cases s with
  | nil => rw [applySubst.eq_1]
  | cons _ _ =>
      rw [applySubst.eq_3]
      · rw [h]
      · intro hc; cases hc

end LogosLab
