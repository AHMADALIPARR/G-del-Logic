/-
  LogosLab.Guards — decidable integrity-constraint guards.
  See MEASURES.md §6. Guards are Bool-valued functions evaluated
  at every extension node BEFORE recursion, inside (future) solve.
  Pruning soundness is a FUTURE theorem (see STATUS.md); the guard
  FUNCTIONS here are executable now.

  Weights are scaled naturals: 1 unit = 0.001 nat of entropy.
  Lean 4.12 core has no Rat; see MEASURES.md §0.
-/

import LogosLab.State

namespace LogosLab

/-- A guard is a decidable predicate on a state. -/
abbrev Guard := State -> Bool

/-- Scaled weight of one hypothesis. -/
abbrev Weight := Nat

/-- Total weight of an explanation: sum of hypothesis weights. -/
def explanationWeight (w : Atom -> Weight) (Δ : List Atom) : Nat :=
  (Δ.map w).foldr (· + ·) 0

/-- Weight/entropy guard: the running weight of the hypotheses
    abduced so far must stay under threshold T. The admissible lower
    bound on remaining goals is 0, because weights are non-negative.
    A non-trivial lower bound is a future refinement. -/
def weightGuard (w : Atom -> Weight) (T : Nat) : Guard :=
  fun st => decide (explanationWeight w st.abduced ≤ T)

/- ------------------------------------------------------------------ -/
/- SEND+MORE=MONEY carry guard.                                       -/
/- Letter codes (Nat, fixed here and nowhere else):                    -/
/-   S = 0, E = 1, N = 2, D = 3, M = 4, O = 5, R = 6, Y = 7           -/
/- An assignment is a list of (letter, digit) pairs, digits 0..9.     -/
/- The guard checks ONLY what is already forced on a partial          -/
/- assignment, so it is a necessary condition for any full solution:  -/
/- a column is checked only when all its letters are assigned, and    -/
/- checking stops at the first column whose carry is unknown.         -/
/- Proving necessity is the blocked lemma                             -/
/- `sendMoreMoneyGuard_necessary` (see STATUS.md).                    -/
/- ------------------------------------------------------------------ -/

/-- An assignment of digits to letters. -/
abbrev Assignment := List (Nat × Nat)

/-- Look up a letter's digit, if assigned. -/
def lookupAssign : Assignment -> Nat -> Option Nat
  | [], _ => none
  | (l, d) :: rest, x => if x = l then some d else lookupAssign rest x

/-- All digits in a list are pairwise distinct. -/
def allDistinct : List Nat -> Bool
  | [] => true
  | x :: xs => !(xs.contains x) && allDistinct xs

/-- No letter is assigned two different digits. -/
def assignmentConsistent : Assignment -> Bool
  | [] => true
  | (l, d) :: rest =>
      (match lookupAssign rest l with
       | none => true
       | some d' => d == d') && assignmentConsistent rest

/-- Check column equations left to right, with exact carry.
    Columns are (left1, left2, result) triples. A column is checked
    only when all three letters are assigned; at the first column
    that cannot be checked, checking stops and returns true (nothing
    forced yet). A checked column that fails returns false. -/
def checkCols (a : Assignment) (carry : Nat) : List (Nat × Nat × Nat) -> Bool
  | [] => true
  | (x, y, z) :: rest =>
      match lookupAssign a x, lookupAssign a y, lookupAssign a z with
      | some dx, some dy, some dz =>
          if (dx + dy + carry) % 10 = dz
          then checkCols a ((dx + dy + carry) / 10) rest
          else false
      | _, _, _ => true

/-- The four SEND+MORE=MONEY columns, units first:
    D + E = Y, N + R = E, E + O = N, S + M = O. -/
def sendMoreMoneyColumns : List (Nat × Nat × Nat) :=
  [(3, 1, 7), (2, 6, 1), (1, 5, 2), (0, 4, 5)]

/-- True iff every letter in the list is assigned. -/
def allAssigned (a : Assignment) (letters : List Nat) : Bool :=
  letters.all fun l => (lookupAssign a l).isSome

/-- Full integer check, used only when all letters are assigned:
    SEND + MORE = MONEY, with leading letters non-zero. -/
def fullSendMoreMoney (a : Assignment) : Bool :=
  match lookupAssign a 0, lookupAssign a 1, lookupAssign a 2, lookupAssign a 3,
        lookupAssign a 4, lookupAssign a 5, lookupAssign a 6, lookupAssign a 7 with
  | some s, some e, some n, some d, some m, some o, some r, some y =>
      s ≠ 0 && m ≠ 0 &&
      (s * 1000 + e * 100 + n * 10 + d) + (m * 1000 + o * 100 + r * 10 + e)
        = (m * 10000 + o * 1000 + n * 100 + e * 10 + y)
  | _, _, _, _, _, _, _, _ => true

/-- The SEND+MORE=MONEY guard: consistent assignment, distinct digits,
    no leading zero for S or M when assigned, every checkable column
    holds with exact carry, and the full equation holds when complete. -/
def sendMoreMoneyGuard (a : Assignment) : Bool :=
  assignmentConsistent a &&
  allDistinct (a.map Prod.snd) &&
  (match lookupAssign a 0 with | none => true | some s => s ≠ 0) &&
  (match lookupAssign a 4 with | none => true | some m => m ≠ 0) &&
  checkCols a 0 sendMoreMoneyColumns &&
  (if allAssigned a [0, 1, 2, 3, 4, 5, 6, 7] then fullSendMoreMoney a else true)

/-- Executable witnesses (not a solver run): the known solution
    S=9, E=5, N=6, D=7, M=1, O=0, R=8, Y=2 passes the guard. -/
def sendMoreMoneySolution : Assignment :=
  [(0, 9), (1, 5), (2, 6), (3, 7), (4, 1), (5, 0), (6, 8), (7, 2)]

/-- A failing partial assignment: D=1, E=2 forces Y=3, not 9. -/
def sendMoreMoneyBadPartial : Assignment :=
  [(3, 1), (1, 2), (7, 9)]

#eval sendMoreMoneyGuard sendMoreMoneySolution
#eval sendMoreMoneyGuard sendMoreMoneyBadPartial

end LogosLab
