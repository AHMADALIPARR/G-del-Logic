-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
/-
  GÖDEL MACHINE KERNEL  (GodelMachine.lean)
  =========================================
  A self-rewriting logic engine whose rewrite gate is a Lean 4 proof
  obligation: candidate code arrives as a Gödel number; it is installed
  only if the kernel finds a machine-checked proof that the rewrite is
  an improvement.  No `sorry`.  No `axiom`.  No foreign code.

  Layers
    0  Prime-factorized pairing   pair a b = 2^a * (2b + 1)
       (2-adic Gödel coding: the exponent of the prime 2 in the code
        IS its tag; bijection proven from induction + omega only)
    1  Deep syntax of the engine  Term / Goal / Rule, Gödel-coded with
       proven encode/decode round-trips
    2  Execution                  fuel-bounded closure over a
       range-restricted Datalog fragment: the universe of derivable
       atoms is finite BY CONSTRUCTION, so termination is data.
    3  Improvement relation       outputs preserved, program strictly
                                 smaller, cost non-increasing
    4  The gate (Gödel machine)   install : Prog -> GödelNumber -> Option Prog
    5  Meta-loop                  improve: self-rewriting with a proved
                                 never-regress theorem

  Verified rewrite inventory: dead-clause elimination.  The gate is
  open-ended: a new rewrite = a new constructor of `ImprovementProof`
  + a new case of `proof_improves`.  Nothing else can be installed.
-/

set_option autoImplicit false

namespace GodelMachine

/- ====================== Layer 0: prime-factorized pairing ====================== -/

def pow2 : Nat → Nat
  | 0     => 1
  | n + 1 => 2 * pow2 n

theorem pow2_pos (n : Nat) : 0 < pow2 n := by
  induction n with
  | zero      => decide
  | succ k ih => simp only [pow2]; omega

/-- 2-adic valuation: exponent of the prime 2 in n (0 at n = 0). -/
def v2 : Nat → Nat
  | 0     => 0
  | n + 1 => if (n + 1) % 2 = 0 then v2 ((n + 1) / 2) + 1 else 0
termination_by n => n
decreasing_by simp_wf; omega

/-- Odd part: n with all factors of 2 removed (0 at n = 0). -/
def oddPart : Nat → Nat
  | 0     => 0
  | n + 1 => if (n + 1) % 2 = 0 then oddPart ((n + 1) / 2) else n + 1
termination_by n => n
decreasing_by simp_wf; omega

theorem v2_succ (k : Nat) :
    v2 (k + 1) = if (k + 1) % 2 = 0 then v2 ((k + 1) / 2) + 1 else 0 := by
  rw [v2]

theorem oddPart_succ (k : Nat) :
    oddPart (k + 1) = if (k + 1) % 2 = 0 then oddPart ((k + 1) / 2) else k + 1 := by
  rw [oddPart]

theorem v2_two_mul {m : Nat} : 0 < m → v2 (2 * m) = v2 m + 1 := by
  intro h
  cases m with
  | zero   => omega
  | succ k =>
      have he : (2 * (k + 1)) % 2 = 0 := by omega
      have hd : (2 * (k + 1)) / 2 = k + 1 := by omega
      have e : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [e, v2_succ, ← e, if_pos he, hd]

theorem oddPart_two_mul {m : Nat} : 0 < m → oddPart (2 * m) = oddPart m := by
  intro h
  cases m with
  | zero   => omega
  | succ k =>
      have he : (2 * (k + 1)) % 2 = 0 := by omega
      have hd : (2 * (k + 1)) / 2 = k + 1 := by omega
      have e : 2 * (k + 1) = (2 * k + 1) + 1 := by omega
      rw [e, oddPart_succ, ← e, if_pos he, hd]

/-- Prime-factorized pairing: the tag lives in the exponent of prime 2. -/
def pair (a b : Nat) : Nat := pow2 a * (2 * b + 1)

def unpair : Nat → Nat × Nat := fun n => (v2 n, (oddPart n - 1) / 2)

theorem v2_pair (a b : Nat) : v2 (pair a b) = a := by
  induction a with
  | zero =>
      show v2 (pow2 0 * (2 * b + 1)) = 0
      have e : pow2 0 * (2 * b + 1) = (2 * b) + 1 := by simp [pow2]
      rw [e, v2_succ, if_neg (by omega)]
  | succ k ih =>
      have e : pow2 (k + 1) * (2 * b + 1) = 2 * (pow2 k * (2 * b + 1)) := by
        simp only [pow2]; rw [Nat.mul_assoc]
      have hpos : 0 < pow2 k * (2 * b + 1) :=
        Nat.mul_pos (pow2_pos k) (by omega)
      show v2 (pow2 (k + 1) * (2 * b + 1)) = k + 1
      rw [e, v2_two_mul hpos]
      exact congrArg (· + 1) ih

theorem odd_part_pair (a b : Nat) : oddPart (pair a b) = 2 * b + 1 := by
  induction a with
  | zero =>
      show oddPart (pow2 0 * (2 * b + 1)) = 2 * b + 1
      have e : pow2 0 * (2 * b + 1) = (2 * b) + 1 := by simp [pow2]
      rw [e, oddPart_succ, if_neg (by omega)]
  | succ k ih =>
      have e : pow2 (k + 1) * (2 * b + 1) = 2 * (pow2 k * (2 * b + 1)) := by
        simp only [pow2]; rw [Nat.mul_assoc]
      have hpos : 0 < pow2 k * (2 * b + 1) :=
        Nat.mul_pos (pow2_pos k) (by omega)
      show oddPart (pow2 (k + 1) * (2 * b + 1)) = 2 * b + 1
      rw [e, oddPart_two_mul hpos]
      exact ih

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  show (v2 (pair a b), (oddPart (pair a b) - 1) / 2) = (a, b)
  rw [v2_pair, odd_part_pair]
  refine Prod.ext rfl ?_
  show (2 * b + 1 - 1) / 2 = b
  omega

theorem v2_le : ∀ n, v2 n ≤ n := by
  intro n
  induction n using Nat.strongInductionOn
  rename_i m ih
  cases m with
  | zero => rw [v2]; exact Nat.le_refl _
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hv : v2 (k + 1) = v2 ((k + 1) / 2) + 1 := by
          have h := v2_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        rw [hv]
        have := ih ((k + 1) / 2) (by omega)
        omega
      · rw [v2_succ, if_neg he]; omega

theorem oddPart_le : ∀ n, oddPart n ≤ n := by
  intro n
  induction n using Nat.strongInductionOn
  rename_i m ih
  cases m with
  | zero => rw [oddPart]; exact Nat.le_refl _
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          have h := oddPart_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        rw [ho]
        have := ih ((k + 1) / 2) (by omega)
        omega
      · rw [oddPart_succ, if_neg he]; exact Nat.le_refl _

theorem oddPart_pos : ∀ {n : Nat}, n ≠ 0 → 0 < oddPart n := by
  intro n
  induction n using Nat.strongInductionOn
  rename_i m ih
  intro hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          have h := oddPart_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        rw [ho]
        exact ih ((k + 1) / 2) (by omega) (by omega)
      · rw [oddPart_succ, if_neg he]; omega

theorem oddPart_odd : ∀ {n : Nat}, n ≠ 0 → oddPart n % 2 = 1 := by
  intro n
  induction n using Nat.strongInductionOn
  rename_i m ih
  intro hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          have h := oddPart_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        rw [ho]
        exact ih ((k + 1) / 2) (by omega) (by omega)
      · rw [oddPart_succ, if_neg he]; omega

/-- Unfolded strict snd-bound (used by decreasing_by blocks). -/
theorem unpair_snd_lt' : ∀ {n : Nat}, n ≠ 0 → (oddPart n - 1) / 2 < n := by
  intro n hn
  cases n with
  | zero   => contradiction
  | succ k =>
      have h1 := oddPart_le (k + 1)
      have h2 := oddPart_pos (by omega : k + 1 ≠ 0)
      omega

/-- Fundamental theorem of the coding: n = 2^(v2 n) * oddPart n. -/
theorem pow2_v2_mul_oddPart : ∀ n, n ≠ 0 → pow2 (v2 n) * oddPart n = n := by
  intro n
  induction n using Nat.strongInductionOn
  rename_i m ih
  intro hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hv : v2 (k + 1) = v2 ((k + 1) / 2) + 1 := by
          have h := v2_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          have h := oddPart_two_mul (m := (k + 1) / 2) (by omega)
          rw [← e] at h
          exact h
        have ih' := ih ((k + 1) / 2) (by omega) (by omega)
        rw [hv, ho]
        show 2 * pow2 (v2 ((k + 1) / 2)) * oddPart ((k + 1) / 2) = k + 1
        rw [Nat.mul_assoc, ih']
        omega
      · have hv : v2 (k + 1) = 0 := by
          rw [v2_succ, if_neg he]
        have ho : oddPart (k + 1) = k + 1 := by
          rw [oddPart_succ, if_neg he]
        rw [hv, ho]
        show 1 * (k + 1) = k + 1
        rw [Nat.one_mul]

theorem pair_unpair {n : Nat} (h : n ≠ 0) : pair (unpair n).1 (unpair n).2 = n := by
  show pow2 (v2 n) * (2 * ((oddPart n - 1) / 2) + 1) = n
  have ho := oddPart_odd h
  have _hp := oddPart_pos h
  have e : 2 * ((oddPart n - 1) / 2) + 1 = oddPart n := by omega
  rw [e]
  exact pow2_v2_mul_oddPart n h

theorem pair_pos (a b : Nat) : pair a b ≠ 0 := by
  have := Nat.mul_pos (pow2_pos a) (by omega : 0 < 2 * b + 1)
  show pow2 a * (2 * b + 1) ≠ 0
  omega


/- ====================== Layer 1: Gödel-coded syntax ====================== -/

inductive Term where
  | var (n : Nat)
  | con (c : Nat)
  | app (f : Nat) (l r : Term)
  deriving DecidableEq, Repr

def codeTerm : Term → Nat
  | Term.var n     => pair 0 n
  | Term.con c     => pair 1 c
  | Term.app f l r => pair 2 (pair f (pair (codeTerm l) (codeTerm r)))

def decodeTerm : Nat → Option Term
  | 0 => none
  | n => match _h : unpair n with
    | (0, b) => some (Term.var b)
    | (1, b) => some (Term.con b)
    | (2, b) => match _h2 : unpair b with
      | (f, lr) => match _h3 : unpair lr with
        | (cl, cr) => match decodeTerm cl, decodeTerm cr with
          | some l, some r => some (Term.app f l r)
          | _, _           => none
    | _ => none
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    have h' : (v2 n, (oddPart n - 1) / 2) = (2, b) := _h
    have h2' : (v2 b, (oddPart b - 1) / 2) = (f, lr) := _h2
    have h3' : (v2 lr, (oddPart lr - 1) / 2) = (cl, cr) := _h3
    injection h' with a1 a2
    injection h3' with c1 c2
    injection h2' with b1 b2
    have hv0 : v2 0 = 0 := by rw [v2]
    have hn : n ≠ 0 := by
      intro e; subst e; omega
    have l1 := unpair_snd_lt' hn
    have l2 := oddPart_le b
    have l3 := v2_le lr
    have l4 := oddPart_le lr
    omega

theorem decodeTerm_codeTerm (t : Term) : decodeTerm (codeTerm t) = some t := by
  induction t with
  | var n =>
      rw [codeTerm, decodeTerm.eq_2 _ (pair_pos 0 n)]
      split
      · rename_i b hb
        rw [unpair_pair] at hb
        injection hb with _ h2; rw [h2]
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i h0 _ _; exact (h0 n (unpair_pair 0 n)).elim
  | con c =>
      rw [codeTerm, decodeTerm.eq_2 _ (pair_pos 1 c)]
      split
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i b hb
        rw [unpair_pair] at hb
        injection hb with _ h2; rw [h2]
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i _ h1 _; exact (h1 c (unpair_pair 1 c)).elim
  | app f l r ihl ihr =>
      rw [codeTerm, decodeTerm.eq_2 _ (pair_pos 2 _)]
      split
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i b hb; rw [unpair_pair] at hb; simp at hb
      · rename_i b hb
        rw [unpair_pair] at hb
        injection hb with _ h2
        subst h2
        split
        · rename_i f' lr h2
          rw [unpair_pair] at h2
          injection h2 with e1 e2
          subst e1; subst e2
          split
          · rename_i cl cr h3
            rw [unpair_pair] at h3
            injection h3 with e1 e2
            subst e1; subst e2
            rw [ihl, ihr]
      · rename_i _ _ h2; exact (h2 _ (unpair_pair 2 _)).elim

/-- Sequence numbers: Gödel-coded lists of naturals (0 codes []). -/
def codeList : List Nat → Nat
  | []      => 0
  | x :: xs => pair (x + 1) (codeList xs)

def decodeList : Nat → Option (List Nat)
  | 0 => some []
  | n + 1 => match _h : unpair (n + 1) with
    | (x, r) => match decodeList r with
      | some l => some ((x - 1) :: l)
      | none   => none
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    have h' : (v2 (n + 1), (oddPart (n + 1) - 1) / 2) = (x, r) := _h
    injection h' with a1 a2
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    omega

theorem decodeList_codeList (l : List Nat) : decodeList (codeList l) = some l := by
  induction l with
  | nil    => rfl
  | cons x xs ih =>
      obtain ⟨m, hm⟩ : ∃ m, pair (x + 1) (codeList xs) = m + 1 :=
        ⟨pair (x + 1) (codeList xs) - 1, by have := pair_pos (x + 1) (codeList xs); omega⟩
      have hu := unpair_pair (x + 1) (codeList xs)
      rw [hm] at hu
      rw [codeList, hm, decodeList]
      split
      · rename_i x' r hb
        rw [hu] at hb
        injection hb with e1 e2
        subst e1; subst e2
        simp only [ih, Nat.add_sub_cancel]

inductive Goal where
  | atom (p : Nat) (args : List Nat)
  deriving DecidableEq, Repr

def codeGoal : Goal → Nat
  | Goal.atom p args => pair p (codeList args)

def decodeGoal : Nat → Option Goal
  | 0 => none
  | n => match unpair n with
    | (p, al) => match decodeList al with
      | some args => some (Goal.atom p args)
      | none      => none

theorem decodeGoal_codeGoal (g : Goal) : decodeGoal (codeGoal g) = some g := by
  cases g with
  | atom p args =>
      rw [codeGoal]
      unfold decodeGoal
      split
      · rename_i h0; exact absurd h0 (pair_pos _ _)
      · rw [unpair_pair]
        dsimp only
        rw [decodeList_codeList]

structure Rule where
  head : Goal
  body : List Goal
  deriving DecidableEq, Repr

def decodeGoals : List Nat → Option (List Goal)
  | []      => some []
  | n :: ns => match decodeGoal n, decodeGoals ns with
    | some g, some gs => some (g :: gs)
    | _, _            => none

theorem decodeGoals_codeGoals (body : List Goal) :
    decodeGoals (body.map codeGoal) = some body := by
  induction body with
  | nil => rfl
  | cons b bs ih =>
      rw [List.map, decodeGoals, decodeGoal_codeGoal, ih]

def codeRule (r : Rule) : Nat :=
  pair (codeGoal r.head + 1) (codeList (r.body.map codeGoal))

def decodeRule : Nat → Option Rule
  | 0 => none
  | n => match unpair n with
    | (h, bl) => if h = 0 then none
        else match decodeGoal (h - 1), decodeList bl with
          | some hd, some bs => match decodeGoals bs with
              | some body => some { head := hd, body := body }
              | none => none
          | _, _ => none

theorem decodeRule_codeRule (r : Rule) : decodeRule (codeRule r) = some r := by
  cases r with
  | mk head body =>
      rw [codeRule]
      unfold decodeRule
      split
      · rename_i h0; exact absurd h0 (pair_pos _ _)
      · rw [unpair_pair]
        dsimp only
        rw [if_neg (by omega)]
        have e : codeGoal head + 1 - 1 = codeGoal head := by omega
        rw [e, decodeGoal_codeGoal, decodeList_codeList]
        simp only [decodeGoals_codeGoals]

def codeProg : List Rule → Nat := codeList ∘ List.map codeRule

def decodeProg : Nat → Option (List Rule)
  | 0 => some []
  | n + 1 => match _h : unpair (n + 1) with
    | (x, r) => match decodeProg r, decodeRule (x - 1) with
      | some rs, some rr => some (rr :: rs)
      | _, _ => none
termination_by n => n
decreasing_by
  all_goals simp_wf
  all_goals
    have h' : (v2 (n + 1), (oddPart (n + 1) - 1) / 2) = (x, r) := _h
    injection h' with a1 a2
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    omega

theorem decodeProg_codeProg (P : List Rule) : decodeProg (codeProg P) = some P := by
  induction P with
  | nil    => rfl
  | cons r rs ih =>
      obtain ⟨m, hm⟩ : ∃ m, pair (codeRule r + 1) (codeProg rs) = m + 1 :=
        ⟨pair (codeRule r + 1) (codeProg rs) - 1,
         by have := pair_pos (codeRule r + 1) (codeProg rs); omega⟩
      have hu := unpair_pair (codeRule r + 1) (codeProg rs)
      rw [hm] at hu
      have hc : codeProg (r :: rs) = m + 1 := by
        rw [← hm]; rfl
      rw [hc, decodeProg]
      split
      · rename_i x' r' hb
        rw [hu] at hb
        injection hb with e1 e2
        subst e1; subst e2
        simp only [ih, Nat.add_sub_cancel, decodeRule_codeRule]

/- ============================ Layer 2: execution =========================== -/

abbrev Prog := List Rule

/-- The machine's birth state (fixed initial database). -/
def seed : List Goal := [Goal.atom 0 [0, 1]]

/-- Element removal (keeps order); no `List.erase` API names anywhere. -/
def remove' {α : Type} [DecidableEq α] (x : α) : List α → List α
  | []     => []
  | y :: t => if y = x then remove' x t else y :: remove' x t

theorem remove'_cons_pos {α : Type} [DecidableEq α] {x a : α} (t : List α)
    (h : a = x) : remove' x (a :: t) = remove' x t := by
  rw [remove', if_pos h]

theorem remove'_cons_neg {α : Type} [DecidableEq α] {x a : α} (t : List α)
    (h : a ≠ x) : remove' x (a :: t) = a :: remove' x t := by
  rw [remove', if_neg h]

theorem notin_remove' {α : Type} [DecidableEq α] {x : α} (l : List α) :
    x ∉ remove' x l := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove', if_pos ha]; exact ih
      · rw [remove', if_neg ha]
        intro h
        rcases List.mem_cons.1 h with h | h
        · exact ha h.symm
        · exact ih h

theorem remove'_sub {α : Type} [DecidableEq α] {x y : α} (l : List α) :
    y ∈ remove' x l → y ∈ l := by
  induction l with
  | nil => intro h; simp [remove'] at h
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove', if_pos ha]; intro h; exact List.Mem.tail a (ih h)
      · rw [remove', if_neg ha]
        intro h
        rcases List.mem_cons.1 h with h | h
        · rw [h]; exact List.Mem.head t
        · exact List.Mem.tail a (ih h)

theorem remove'_notin {α : Type} [DecidableEq α] {x : α} {l : List α}
    (h : x ∉ l) : remove' x l = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases ha : a = x
      · exact (h (by rw [← ha]; exact List.Mem.head t)).elim
      · rw [remove', if_neg ha, ih (fun hx => h (List.Mem.tail a hx))]

theorem length_remove'_le {α : Type} [DecidableEq α] (x : α) (l : List α) :
    (remove' x l).length ≤ l.length := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove', if_pos ha, List.length_cons]; omega
      · rw [remove', if_neg ha, List.length_cons, List.length_cons]; omega

theorem length_remove' {α : Type} [DecidableEq α] {x : α} {l : List α}
    (h : x ∈ l) : (remove' x l).length ≤ l.length - 1 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove'_cons_pos t ha, List.length_cons]
        have := length_remove'_le x t
        omega
      · rw [remove'_cons_neg t ha]
        cases h with
        | head => exact absurd rfl ha
        | tail _ h =>
            have hp := List.length_pos_of_mem h
            have := ih h
            rw [List.length_cons, List.length_cons]; omega

theorem mem_remove' {α : Type} [DecidableEq α] {x y : α} {l : List α}
    (hn : y ≠ x) : y ∈ remove' x l ↔ y ∈ l := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove'_cons_pos t ha]
        constructor
        · intro h; exact List.Mem.tail a (ih.1 h)
        · intro h
          rcases List.mem_cons.1 h with h | h
          · exact absurd (h.trans ha) hn
          · exact ih.2 h
      · rw [remove'_cons_neg t ha, List.mem_cons, List.mem_cons, ih]

theorem remove'_idem {α : Type} [DecidableEq α] (x : α) (l : List α) :
    remove' x (remove' x l) = remove' x l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases ha : a = x
      · rw [remove'_cons_pos t ha]; exact ih
      · rw [remove'_cons_neg t ha, remove'_cons_neg _ ha, ih]

theorem remove'_comm {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y)
    (l : List α) : remove' x (remove' y l) = remove' y (remove' x l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases hay : a = y <;> by_cases hax : a = x
      · exact absurd (hax.symm.trans hay) h
      · rw [remove'_cons_pos t hay, remove'_cons_neg t hax, remove'_cons_pos _ hay, ih]
      · rw [remove'_cons_neg t hay, remove'_cons_pos _ hax, remove'_cons_pos t hax, ih]
      · rw [remove'_cons_neg t hay, remove'_cons_neg _ hax, remove'_cons_neg t hax,
            remove'_cons_neg _ hay, ih]

/-- Duplicate-free list, FIRST occurrence kept.  Structural recursion.
    First-occurrence dedup is what makes every closure step a strict
    PREFIX extension (see dfl_append_prefix), which is what makes the
    chain-length / pigeonhole fixpoint argument sound. -/
def nodup' {α : Type} [DecidableEq α] : List α → List α
  | []     => []
  | x :: t => x :: remove' x (nodup' t)

theorem remove'_dfl {α : Type} [DecidableEq α] (x : α) (l : List α) :
    remove' x (nodup' l) = nodup' (remove' x l) := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      by_cases hyx : y = x
      · subst hyx
        show remove' y (y :: remove' y (nodup' t)) = nodup' (remove' y (y :: t))
        rw [remove'_cons_pos _ rfl, remove'_cons_pos _ rfl, remove'_idem, ih]
      · show remove' x (y :: remove' y (nodup' t)) = nodup' (remove' x (y :: t))
        rw [remove'_cons_neg _ hyx, remove'_cons_neg _ hyx]
        show y :: remove' x (remove' y (nodup' t)) = y :: remove' y (nodup' (remove' x t))
        rw [remove'_comm (Ne.symm hyx), ih]

theorem mem_nodup' {α : Type} [DecidableEq α] (x : α) (l : List α) :
    x ∈ nodup' l ↔ x ∈ l := by
  induction l with
  | nil => simp [nodup']
  | cons y t ih =>
      show (x ∈ y :: remove' y (nodup' t)) ↔ (x ∈ y :: t)
      rw [List.mem_cons, List.mem_cons]
      constructor
      · rintro (rfl | h)
        · left; rfl
        · by_cases hxy : x = y
          · left; exact hxy
          · right; exact ih.1 ((mem_remove' hxy).1 h)
      · rintro (rfl | h)
        · left; rfl
        · by_cases hxy : x = y
          · subst hxy; left; rfl
          · right; exact (mem_remove' hxy).2 (ih.2 h)

theorem length_nodup'_le {α : Type} [DecidableEq α] (l : List α) :
    (nodup' l).length ≤ l.length := by
  induction l with
  | nil => simp [nodup']
  | cons y t ih =>
      show (y :: remove' y (nodup' t)).length ≤ (y :: t).length
      have h1 := length_remove'_le y (nodup' t)
      rw [List.length_cons, List.length_cons]
      omega

theorem remove'_append {α : Type} [DecidableEq α] {x : α} {a b : List α}
    (h : x ∉ a) : remove' x (a ++ b) = a ++ remove' x b := by
  induction a with
  | nil => rfl
  | cons y t ih =>
      have hyn : y ≠ x := fun e => h (e ▸ List.Mem.head t)
      have hxt : x ∉ t := fun hx => h (List.Mem.tail y hx)
      rw [List.cons_append, List.cons_append, remove'_cons_neg _ hyn, ih hxt]

/-- THE KEY PREFIX LEMMA: appending to a duplicate-free list, then
    de-duplicating with first-occurrence keeping, yields the original
    list as a prefix.  This makes the closure chain strictly growing. -/
theorem dfl_append_prefix {α : Type} [DecidableEq α] :
    ∀ (a m : List α), a = nodup' a → ∃ r, nodup' (a ++ m) = a ++ r := by
  intro a
  induction a with
  | nil => intro m _; exact ⟨nodup' m, rfl⟩
  | cons x t ih =>
      intro m ha
      have h1 : x :: remove' x (nodup' t) = x :: t := ha.symm
      injection h1 with _ h2
      have hxn : x ∉ t := by
        intro hx
        exact notin_remove' (nodup' t) (by rw [h2]; exact hx)
      have ht : t = nodup' t := by
        have hxn' : x ∉ nodup' t := fun hx => hxn ((mem_nodup' x t).1 hx)
        rw [remove'_notin hxn'] at h2
        exact h2.symm
      obtain ⟨r, hr⟩ := ih m ht
      refine ⟨remove' x r, ?_⟩
      show x :: remove' x (nodup' (t ++ m)) = x :: t ++ remove' x r
      rw [hr, remove'_append hxn, List.cons_append]

/-- The pigeonhole core: subsets of duplicate-free lists are no longer. -/
theorem length_le_of_subset {α : Type} [DecidableEq α] {a b : List α}
    (ha : a = nodup' a) (hb : b = nodup' b)
    (h : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a generalizing b with
  | nil => simp
  | cons x t ih =>
      have hxn : x ∉ t := by
        have h1 : x :: remove' x (nodup' t) = x :: t := ha.symm
        injection h1 with _ h2
        intro hx
        exact notin_remove' (nodup' t) (by rw [h2]; exact hx)
      have ht : t = nodup' t := by
        have h1 : x :: remove' x (nodup' t) = x :: t := ha.symm
        injection h1 with _ h2
        have hxn' : x ∉ nodup' t := fun hx => hxn ((mem_nodup' x t).1 hx)
        rw [remove'_notin hxn'] at h2
        exact h2.symm
      have hxb : x ∈ b := h x (List.Mem.head t)
      have hrem : ∀ y ∈ t, y ∈ remove' x b := by
        intro y hy
        have hyb := h y (List.Mem.tail x hy)
        have hyn : y ≠ x := fun e => hxn (e ▸ hy)
        exact (mem_remove' hyn).2 hyb
      have hb' : remove' x b = nodup' (remove' x b) := by
        exact (congrArg (remove' x) hb).trans (remove'_dfl x b)
      have hle := ih ht hb' hrem
      have hlr := length_remove' hxb
      have hp := List.length_pos_of_mem hxb
      rw [List.length_cons]
      omega

/- ---- list splitting at an index (structural; no List.take/drop names) ----/

def dropIx {α : Type} : List α → Nat → List α
  | [],     _     => []
  | _ :: t, 0     => t
  | x :: t, n + 1 => x :: dropIx t n

theorem split_at {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    ∃ l₁ r l₂, l = l₁ ++ r :: l₂ ∧ l₁.length = i ∧ dropIx l i = l₁ ++ l₂ ∧ r = l.get ⟨i, h⟩ := by
  induction i generalizing l with
  | zero =>
      cases l with
      | nil => simp at h
      | cons x t => exact ⟨[], x, t, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      cases l with
      | nil => exact absurd h (Nat.not_lt_zero _)
      | cons x t =>
          have hn : n < t.length := Nat.lt_of_succ_lt_succ h
          obtain ⟨l₁, r, l₂, he, hl1, hd, hget⟩ := ih t hn
          refine ⟨x :: l₁, r, l₂, ?_, ?_, ?_, ?_⟩
          · rw [he]; rfl
          · simp; exact hl1
          · show x :: dropIx t n = (x :: l₁) ++ l₂
            rw [hd]; rfl
          · exact hget

theorem length_dropIx {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (dropIx l i).length = l.length - 1 := by
  obtain ⟨l₁, r, l₂, he, hl1, hd, _⟩ := split_at l i h
  rw [hd, List.length_append]
  have hlen : l.length = (l₁ ++ r :: l₂).length := by rw [he]
  rw [List.length_append] at hlen
  simp at hlen
  omega

theorem dropIx_sub {α : Type} (l : List α) (i : Nat) :
    ∀ x ∈ dropIx l i, x ∈ l := by
  induction l generalizing i with
  | nil => intro x hx; simp [dropIx] at hx
  | cons y t ih =>
      intro x hx
      cases i with
      | zero => exact List.Mem.tail y hx
      | succ n =>
          have hx' : x ∈ y :: dropIx t n := hx
          rcases List.mem_cons.1 hx' with hx | hx
          · rw [hx]; exact List.Mem.head _
          · exact List.Mem.tail y (ih n x hx)

/- ---- the evaluator ----/

/-- All atoms a program can ever mention (heads plus bodies). -/
def atomsOf : Prog → List Goal
  | []      => []
  | r :: rs => r.head :: (r.body ++ atomsOf rs)

/-- Finite universe of derivable atoms: termination is data. -/
def universe_ (P : Prog) : List Goal := nodup' (seed ++ atomsOf P)

theorem nodup'_idem {α : Type} [DecidableEq α] (l : List α) :
    nodup' (nodup' l) = nodup' l := by
  induction l with
  | nil => rfl
  | cons y t ih =>
      show y :: remove' y (nodup' (remove' y (nodup' t))) = y :: remove' y (nodup' t)
      rw [remove'_dfl y (remove' y (nodup' t)), remove'_idem y (nodup' t),
        ← remove'_dfl y (nodup' t), ih]

theorem universe_fix (P : Prog) : universe_ P = nodup' (universe_ P) :=
  (nodup'_idem _).symm

theorem seed_sub_universe (P : Prog) : ∀ x ∈ seed, x ∈ universe_ P := by
  intro x hx
  apply (mem_nodup' x (seed ++ atomsOf P)).2
  exact List.mem_append.2 (Or.inl hx)

def memAll (db : List Goal) : List Goal → Bool
  | []     => true
  | g :: t => (decide (g ∈ db)) && memAll db t

def applicable (db : List Goal) (r : Rule) : Bool := memAll db r.body

theorem memAll_false {db : List Goal} {g : Goal} {l : List Goal}
    (h1 : g ∈ l) (h2 : g ∉ db) : memAll db l = false := by
  induction l with
  | nil => simp at h1
  | cons a t ih =>
      show (decide (a ∈ db) && memAll db t) = false
      by_cases ha : a ∈ db
      · rcases List.mem_cons.1 h1 with h1 | h1
        · exact absurd (h1 ▸ ha) h2
        · rw [decide_eq_true ha, Bool.true_and]
          exact ih h1
      · rw [decide_eq_false ha, Bool.false_and]

theorem memAll_true {db : List Goal} {l : List Goal}
    (h : ∀ g ∈ l, g ∈ db) : memAll db l = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      show (decide (a ∈ db) && memAll db t) = true
      rw [decide_eq_true (h a (List.Mem.head t)), Bool.true_and]
      exact ih (fun g hg => h g (List.Mem.tail a hg))

theorem memAll_spec {db : List Goal} {l : List Goal}
    (h : memAll db l = true) : ∀ g ∈ l, g ∈ db := by
  induction l with
  | nil => intro g hg; simp at hg
  | cons a t ih =>
      intro g hg
      have h2 : (decide (a ∈ db) && memAll db t) = true := h
      simp only [Bool.and_eq_true] at h2
      rcases List.mem_cons.1 hg with hg | hg
      · rw [hg]; exact of_decide_eq_true h2.1
      · exact ih h2.2 _ hg

theorem applicable_mono {db db' : List Goal} (h : ∀ x ∈ db, x ∈ db')
    (r : Rule) (ha : applicable db r = true) : applicable db' r = true :=
  memAll_true (fun g hg => h g (memAll_spec ha g hg))

def stepAdd (db : List Goal) (r : Rule) (acc : List Goal) : List Goal :=
  if applicable db r then r.head :: acc else acc

theorem stepAdd_mem {db r acc y} (h : y ∈ stepAdd db r acc) :
    (applicable db r = true ∧ y = r.head) ∨ y ∈ acc := by
  unfold stepAdd at h
  by_cases ha : applicable db r = true
  · simp only [ha, if_true, List.mem_cons] at h
    rcases h with h | h
    · exact Or.inl ⟨ha, h⟩
    · exact Or.inr h
  · have hn : applicable db r = false := by
      cases hbb : applicable db r with
      | true  => simp_all
      | false => rfl
    simp only [hn, if_false] at h
    exact Or.inr h

def closureStep (P : Prog) (db : List Goal) : List Goal :=
  nodup' (db ++ P.foldr (stepAdd db) [])

theorem closureStep_sub_universe (P : Prog) (db : List Goal)
    (hdb : ∀ x ∈ db, x ∈ universe_ P) :
    ∀ x ∈ closureStep P db, x ∈ universe_ P := by
  intro x hx
  rw [closureStep, mem_nodup'] at hx
  have key : ∀ Q : Prog, ∀ y ∈ Q.foldr (stepAdd db) [], y ∈ atomsOf Q := by
    intro Q
    induction Q with
    | nil => intro y hy; simp [List.foldr] at hy
    | cons r rs ih =>
        intro y hy
        have hy2 : y ∈ stepAdd db r (rs.foldr (stepAdd db) []) := hy
        rcases stepAdd_mem hy2 with ⟨_, he⟩ | hy'
        · rw [he]; exact List.Mem.head _
        · exact List.mem_cons.2 (Or.inr (List.mem_append.2 (Or.inr (ih y hy'))))
  rcases (List.mem_append.1 hx) with hx | hx
  · exact hdb x hx
  · exact (mem_nodup' x (seed ++ atomsOf P)).2 (List.mem_append.2 (Or.inr (key P x hx)))

theorem closureStep_infl (P : Prog) (db : List Goal) :
    ∀ x ∈ db, x ∈ closureStep P db := by
  intro x hx
  rw [closureStep, mem_nodup']
  exact List.mem_append.2 (Or.inl hx)

theorem closureStep_monotone {P} {db db'} (h : ∀ x ∈ db, x ∈ db') :
    ∀ x ∈ closureStep P db, x ∈ closureStep P db' := by
  intro x hx
  rw [closureStep] at hx ⊢
  rw [mem_nodup'] at hx ⊢
  have key : ∀ Q : Prog, ∀ y ∈ Q.foldr (stepAdd db) [], y ∈ Q.foldr (stepAdd db') [] := by
    intro Q
    induction Q with
    | nil => intro y hy; simp [List.foldr] at hy
    | cons r rs ih =>
        intro y hy
        have hy2 : y ∈ stepAdd db r (rs.foldr (stepAdd db) []) := hy
        show y ∈ stepAdd db' r (rs.foldr (stepAdd db') [])
        rcases stepAdd_mem hy2 with ⟨ha, he⟩ | hy'
        · rw [he]; unfold stepAdd; rw [if_pos (applicable_mono h r ha)]
          exact List.Mem.head _
        · unfold stepAdd
          by_cases hb : applicable db' r = true
          · rw [if_pos hb]; exact List.Mem.tail _ (ih y hy')
          · rw [if_neg hb]; exact ih y hy'
  rcases (List.mem_append.1 hx) with hx | hx
  · exact List.mem_append.2 (Or.inl (h x hx))
  · exact List.mem_append.2 (Or.inr (key P x hx))

def closure : Nat → Prog → List Goal → List Goal
  | 0,     _, db => db
  | n + 1, P, db => closure n P (closureStep P db)

theorem closure_infl (P : Prog) : ∀ fuel db, ∀ x ∈ db, x ∈ closure fuel P db := by
  intro fuel
  induction fuel with
  | zero => intro db x hx; exact hx
  | succ _ ih =>
      intro db x hx
      exact ih _ x (closureStep_infl P db x hx)

theorem closure_sub_universe (P : Prog) :
    ∀ fuel db, (∀ x ∈ db, x ∈ universe_ P) →
      ∀ x ∈ closure fuel P db, x ∈ universe_ P := by
  intro fuel
  induction fuel with
  | zero => intro db h x hx; exact h x hx
  | succ n ih =>
      intro db h x hx
      exact ih _ (closureStep_sub_universe P db h) x hx

theorem seed_fix : seed = nodup' seed := rfl

/-- Iteration and one step commute. -/
theorem closureStep_closure : ∀ b (P : Prog) (db : List Goal),
    closure b P (closureStep P db) = closureStep P (closure b P db) := by
  intro b
  induction b with
  | zero => intro P db; rfl
  | succ n ih =>
      intro P db
      show closure n P (closureStep P (closureStep P db)) =
           closureStep P (closure n P (closureStep P db))
      rw [ih]

theorem closure_fixpoint (P : Prog) : ∀ fuel,
    closure fuel P seed = nodup' (closure fuel P seed) := by
  intro fuel
  cases fuel with
  | zero => exact seed_fix
  | succ n =>
      show closure n P (closureStep P seed) = nodup' (closure n P (closureStep P seed))
      rw [closureStep_closure]
      exact (nodup'_idem _).symm

/-- Iteration splits: closure (a+b) = closure a ∘ closure b. -/
theorem closure_add : ∀ a b (P : Prog) (db : List Goal),
    closure (a + b) P db = closure a P (closure b P db) := by
  intro a
  induction a with
  | zero => intro b P db; rw [Nat.zero_add]; rfl
  | succ n ih =>
      intro b P db
      have e : n + 1 + b = (n + b) + 1 := by omega
      rw [e]
      show closure (n + b) P (closureStep P db) = closure n P (closureStep P (closure b P db))
      rw [ih, closureStep_closure]

/-- Every closure step is a strict PREFIX extension: unequal steps are
    strictly longer, so the chain cannot cycle or reorder. -/
theorem closure_succ_append (P : Prog) : ∀ k,
    ∃ m, closure (k + 1) P seed = closure k P seed ++ m := by
  intro k
  induction k with
  | zero =>
      show ∃ m, closureStep P seed = seed ++ m
      exact dfl_append_prefix seed (P.foldr (stepAdd seed) []) seed_fix
  | succ n _ =>
      have hfix := closure_fixpoint P (n + 1)
      obtain ⟨r, hr⟩ := dfl_append_prefix (closure (n + 1) P seed)
                        (P.foldr (stepAdd (closure (n + 1) P seed)) []) hfix
      refine ⟨r, ?_⟩
      show closure (n + 1) P (closureStep P seed) = closure (n + 1) P seed ++ r
      rw [closureStep_closure]
      exact hr

/-- STABILITY (pigeonhole): closure reaches a list fixpoint within bound. -/
def bound (P : Prog) : Nat := (universe_ P).length + 1

theorem exists_fixpoint (P : Prog) :
    ∃ k, k < bound P ∧ closure k P seed = closure (k + 1) P seed := by
  refine Decidable.byContradiction (fun h => ?_)
  have h' : ∀ k, k < bound P → closure k P seed ≠ closure (k + 1) P seed :=
    fun k hk e => h ⟨k, hk, e⟩
  have hpre := closure_succ_append P
  have hlt : ∀ k, k < bound P →
      (closure k P seed).length < (closure (k + 1) P seed).length := by
    intro k hk
    obtain ⟨r, hr⟩ := hpre k
    have hrn : r ≠ [] := by
      intro e
      rw [e, List.append_nil] at hr
      exact h' k hk hr.symm
    rw [hr]
    cases r with
    | nil => contradiction
    | cons x xs => rw [List.length_append, List.length_cons]; omega
  have hge : ∀ k, k ≤ bound P → k ≤ (closure k P seed).length := by
    intro k hk
    induction k with
    | zero => omega
    | succ n ih =>
        have h1 := hlt n (by omega)
        have h2 := ih (by omega)
        omega
  have hU : ∀ x ∈ closure (bound P) P seed, x ∈ universe_ P :=
    closure_sub_universe P (bound P) seed (seed_sub_universe P)
  have hle := length_le_of_subset (closure_fixpoint P (bound P)) (universe_fix P) hU
  have hbig := hge (bound P) (Nat.le_refl _)
  have hb : bound P = (universe_ P).length + 1 := rfl
  omega

/-- A fixpoint equality at n propagates to every m ≥ n. -/
theorem propagate (P : Prog) (n : Nat)
    (H : closure n P seed = closure (n + 1) P seed) :
    ∀ m, n ≤ m → closure m P seed = closure (m + 1) P seed := by
  intro m hm
  induction m with
  | zero =>
      have : n = 0 := by omega
      subst this
      exact H
  | succ k ih =>
      by_cases hkn : n ≤ k
      · have h1 := ih hkn
        have h2 := congrArg (closureStep P) h1
        rw [← closureStep_closure, ← closureStep_closure] at h2
        exact h2
      · have : n = k + 1 := by omega
        subst this
        exact H

def outputs (P : Prog) : List Goal := closure (bound P) P seed

/-- The closure at `bound P` is a genuine step-fixpoint. -/
theorem outputs_fix (P : Prog) : closureStep P (outputs P) = outputs P := by
  obtain ⟨k, hk, hfix⟩ := exists_fixpoint P
  have hB := propagate P k hfix (bound P) (Nat.le_of_lt hk)
  show closureStep P (closure (bound P) P seed) = closure (bound P) P seed
  rw [← closureStep_closure]
  show closure (bound P + 1) P seed = closure (bound P) P seed
  exact hB.symm

/-- A step-fixpoint is immune to further closure. -/
theorem fixpoint_stable (P : Prog) (db : List Goal)
    (h : closureStep P db = db) : ∀ fuel, closure fuel P db = db := by
  intro fuel
  induction fuel with
  | zero => rfl
  | succ n ih =>
      show closure n P (closureStep P db) = db
      rw [h]
      exact ih

/- ---- dead-clause elimination is semantics- and cost-preserving ----/

theorem foldr_skip {α β : Type} (F : α → β → β) (l₁ l₂ : List α) (r : α)
    (init : β) (h : ∀ acc, F r acc = acc) :
    (l₁ ++ r :: l₂).foldr F init = (l₁ ++ l₂).foldr F init := by
  induction l₁ with
  | nil => rw [List.nil_append, List.nil_append]; exact h _
  | cons a t ih =>
      rw [List.cons_append, List.cons_append]
      show F a ((t ++ r :: l₂).foldr F init) = F a ((t ++ l₂).foldr F init)
      rw [ih]

theorem closureStep_erase_dead (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P)
    (db : List Goal) (hdb : ∀ x ∈ db, x ∈ outputs P) :
    closureStep P db = closureStep (dropIx P i) db := by
  obtain ⟨g, hgm, hgd⟩ := hd
  have hgnodb : g ∉ db := fun h => hgd (hdb g h)
  have hap : applicable db (P.get ⟨i, hi⟩) = false := memAll_false hgm hgnodb
  obtain ⟨l₁, r, l₂, he, _, hd2, hget⟩ := split_at P i hi
  subst he
  have hap' : applicable db r = false := by rw [hget]; exact hap
  show nodup' (db ++ (l₁ ++ r :: l₂).foldr (stepAdd db) []) =
       nodup' (db ++ (dropIx (l₁ ++ r :: l₂) i).foldr (stepAdd db) [])
  rw [hd2, foldr_skip (stepAdd db) l₁ l₂ r [] (fun acc => by simp [stepAdd, hap'])]

theorem closure_erase_dead (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P) :
    ∀ fuel db, (∀ x ∈ db, x ∈ outputs P) →
      closure fuel P db = closure fuel (dropIx P i) db := by
  intro fuel
  induction fuel with
  | zero => intro db _; rfl
  | succ n ih =>
      intro db hdb
      show closure n P (closureStep P db) = closure n (dropIx P i) (closureStep (dropIx P i) db)
      rw [closureStep_erase_dead P i hi hd db hdb]
      apply ih
      intro x hx
      have h1 := closureStep_monotone hdb x hx
      have h2 := closureStep_erase_dead P i hi hd (outputs P) (fun y hy => hy)
      rw [← h2, outputs_fix P] at h1
      exact h1

theorem atomsOf_mono_drop (P : Prog) (i : Nat) (hi : i < P.length) :
    ∀ x ∈ atomsOf (dropIx P i), x ∈ atomsOf P := by
  induction P generalizing i with
  | nil => exact absurd hi (Nat.not_lt_zero _)
  | cons r rs ih =>
      intro x hx
      cases i with
      | zero => exact List.Mem.tail r.head (List.mem_append.2 (Or.inr hx))
      | succ n =>
          have hin : n < rs.length := Nat.lt_of_succ_lt_succ hi
          simp only [dropIx, atomsOf, List.mem_cons, List.mem_append] at hx ⊢
          rcases hx with rfl | h | h
          · left; rfl
          · right; left; exact h
          · right; right; exact ih n hin x h

theorem universe_mono (P : Prog) (i : Nat) (hi : i < P.length) :
    ∀ x ∈ universe_ (dropIx P i), x ∈ universe_ P := by
  intro x hx
  rw [universe_, mem_nodup'] at hx ⊢
  rcases List.mem_append.1 hx with hx | hx
  · exact List.mem_append.2 (Or.inl hx)
  · apply List.mem_append.2; right
    exact atomsOf_mono_drop P i hi x hx

theorem outputs_erase_dead (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P) :
    outputs (dropIx P i) = outputs P := by
  have hstep := closure_erase_dead P i hi hd
  have hbig := hstep (bound P) seed (closure_infl P (bound P) seed)
  have hbb : bound (dropIx P i) ≤ bound P := by
    have hsub := universe_mono P i hi
    have hle := length_le_of_subset (universe_fix (dropIx P i)) (universe_fix P) hsub
    show (universe_ (dropIx P i)).length + 1 ≤ (universe_ P).length + 1
    omega
  have hboth : closure (bound P) (dropIx P i) seed =
      closure (bound (dropIx P i)) (dropIx P i) seed := by
    rw [show bound P = (bound P - bound (dropIx P i)) + bound (dropIx P i) from by omega,
        closure_add]
    exact fixpoint_stable (dropIx P i) _ (outputs_fix (dropIx P i)) _
  show closure (bound (dropIx P i)) (dropIx P i) seed = closure (bound P) P seed
  rw [hbig, hboth]

/- ==================== Layer 3: improvement relation ======================== -/

def cost (P : Prog) : Nat := (universe_ P).length - (outputs P).length

theorem cost_le (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P) :
    cost (dropIx P i) ≤ cost P := by
  have hsub := universe_mono P i hi
  have hle := length_le_of_subset (universe_fix (dropIx P i)) (universe_fix P) hsub
  have heq := outputs_erase_dead P i hi hd
  show (universe_ (dropIx P i)).length - (outputs (dropIx P i)).length ≤
       (universe_ P).length - (outputs P).length
  rw [heq]; omega

def Improvement (P P' : Prog) : Prop :=
  outputs P' = outputs P ∧ P'.length < P.length ∧ cost P' ≤ cost P

theorem dropIx_improvement (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P) :
    Improvement P (dropIx P i) :=
  ⟨outputs_erase_dead P i hi hd, by have h1 := length_dropIx P i hi; omega, cost_le P i hi hd⟩

/- ==================== Layer 4: the Gödel machine gate ======================= -/

/-- Proof-carrying rewrite: every installed rewrite must come with one. -/
structure ImprovementProof (P P' : Prog) where
  idx   : Nat
  hi    : idx < P.length
  wit   : Goal
  hwit  : wit ∈ (P.get ⟨idx, hi⟩).body
  hdead : wit ∉ outputs P
  eq    : P' = dropIx P idx

def findDead (P : Prog) : (body : List Goal) →
    Option (Σ' (g : Goal), g ∈ body ∧ g ∉ outputs P)
  | []     => none
  | g :: t => if h : g ∉ outputs P
      then some ⟨g, ⟨List.Mem.head t, h⟩⟩
      else match findDead P t with
        | none => none
        | some ⟨g', hm, hd⟩ => some ⟨g', ⟨List.Mem.tail g hm, hd⟩⟩

def checkIx (P P' : Prog) (i : Nat) (hi : i < P.length) : Option (ImprovementProof P P') :=
  if hEq : P' = dropIx P i then
    match findDead P (P.get ⟨i, hi⟩).body with
    | some ⟨g, hm, hd⟩ => some ⟨i, hi, g, hm, hd, hEq⟩
    | none => none
  else none

def tryAll (P P' : Prog) : (fuel : Nat) → fuel ≤ P.length → Option (ImprovementProof P P')
  | 0,     _  => none
  | k + 1, hf => match checkIx P P' k (Nat.lt_of_lt_of_le (Nat.lt_succ_self k) hf) with
      | some prf => some prf
      | none     => tryAll P P' k (Nat.le_of_succ_le hf)

/-- install: decode the candidate Gödel number, then demand a proof. -/
def install (P : Prog) (g : Nat) : Option Prog :=
  match decodeProg g with
  | some P' => match tryAll P P' P.length (Nat.le_refl _) with
      | some _ => some P'
      | none => none
  | none => none

theorem proof_improves {P P' : Prog} (prf : ImprovementProof P P') : Improvement P P' := by
  rw [prf.eq]
  exact dropIx_improvement P prf.idx prf.hi ⟨prf.wit, prf.hwit, prf.hdead⟩

/-- THE GATE THEOREM: anything installable is an improvement. -/
theorem install_improves (P P' : Prog) (g : Nat) (h : install P g = some P') :
    Improvement P P' := by
  unfold install at h
  cases hg : decodeProg g with
  | none => rw [hg] at h; simp at h
  | some P'' =>
    rw [hg] at h
    dsimp only at h
    cases ht : tryAll P P'' P.length (Nat.le_refl _) with
    | none => rw [ht] at h; simp at h
    | some prf =>
      rw [ht] at h
      injection h with hEq
      subst hEq
      exact proof_improves prf

/- ==================== Layer 5: the self-rewriting loop ===================== -/

def improve : Nat → Prog → List Nat → Prog
  | 0,        P, _  => P
  | _ + 1, P, [] => P
  | fuel + 1, P, c :: cs =>
      match install P c with
      | some P' => improve fuel P' cs
      | none    => improve fuel P cs

/-- THE NEVER-REGRESS THEOREM: self-rewriting cannot make things worse. -/
theorem improve_never_regresses : ∀ fuel P cs,
    (improve fuel P cs).length ≤ P.length ∧
    outputs (improve fuel P cs) = outputs P := by
  intro fuel
  induction fuel with
  | zero => intro P cs; exact ⟨Nat.le_refl _, rfl⟩
  | succ n ih =>
      intro P cs
      cases cs with
      | nil => exact ⟨Nat.le_refl _, rfl⟩
      | cons c t =>
          cases hi : install P c with
          | none => simp only [improve, hi]; exact ih P t
          | some P' =>
            simp only [improve, hi]
            obtain ⟨h1, h2⟩ := ih P' t
            obtain ⟨ho, hl, _⟩ := install_improves P P' c hi
            exact ⟨Nat.le_trans h1 (Nat.le_of_lt hl), by rw [h2, ho]⟩

/- ================================== demo ==================================== -/

def prog0 : Prog := [ ⟨Goal.atom 1 [], []⟩,
                      ⟨Goal.atom 2 [], [Goal.atom 0 []]⟩ ]

/-- The candidate rewrite, delivered as a Gödel number. -/
def prog1 : Prog := dropIx prog0 1

#eval install prog0 (codeProg prog1) == some prog1
#eval (improve 3 prog0 [0, codeProg prog1]).length
#eval outputs prog0 == outputs (improve 3 prog0 [0, codeProg prog1])

#print axioms improve_never_regresses
#print axioms install_improves
#print axioms outputs_erase_dead
#print axioms decodeProg_codeProg
#print axioms pair_unpair

end GodelMachine
