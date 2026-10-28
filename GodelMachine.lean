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
termination_by v2 n => n
decreasing_by omega

/-- Odd part: n with all factors of 2 removed (0 at n = 0). -/
def oddPart : Nat → Nat
  | 0     => 0
  | n + 1 => if (n + 1) % 2 = 0 then oddPart ((n + 1) / 2) else n + 1
termination_by oddPart n => n
decreasing_by omega

theorem v2_two_mul {m : Nat} : 0 < m → v2 (2 * m) = v2 m + 1 := by
  intro h
  cases m with
  | zero   => omega
  | succ k =>
      have he : (2 * (k + 1)) % 2 = 0 := by omega
      have hd : (2 * (k + 1)) / 2 = k + 1 := by omega
      show (if (2 * (k + 1)) % 2 = 0 then v2 ((2 * (k + 1)) / 2) + 1 else 0) = v2 (k + 1) + 1
      rw [if_pos he, hd]

theorem oddPart_two_mul {m : Nat} : 0 < m → oddPart (2 * m) = oddPart m := by
  intro h
  cases m with
  | zero   => omega
  | succ k =>
      have he : (2 * (k + 1)) % 2 = 0 := by omega
      have hd : (2 * (k + 1)) / 2 = k + 1 := by omega
      show (if (2 * (k + 1)) % 2 = 0 then oddPart ((2 * (k + 1)) / 2) else 2 * (k + 1)) = oddPart (k + 1)
      rw [if_pos he, hd]

/-- Prime-factorized pairing: the tag lives in the exponent of prime 2. -/
def pair (a b : Nat) : Nat := pow2 a * (2 * b + 1)

def unpair : Nat → Nat × Nat := fun n => (v2 n, (oddPart n - 1) / 2)

theorem v2_pair (a b : Nat) : v2 (pair a b) = a := by
  induction a with
  | zero =>
      show v2 (pow2 0 * (2 * b + 1)) = 0
      show v2 (1 * (2 * b + 1)) = 0
      show v2 (2 * b + 1) = 0
      have ho : (2 * b + 1) % 2 = 1 := by omega
      show (if (2 * b + 1) % 2 = 0 then v2 ((2 * b + 1) / 2) + 1 else 0) = 0
      rw [if_neg (by omega)]
  | succ k ih =>
      show v2 (pow2 (k + 1) * (2 * b + 1)) = k + 1
      show v2 (2 * (pow2 k * (2 * b + 1))) = k + 1
      have hpos : 0 < pow2 k * (2 * b + 1) := by
        have := pow2_pos k; omega
      rw [v2_two_mul hpos, ih]

theorem odd_part_pair (a b : Nat) : oddPart (pair a b) = 2 * b + 1 := by
  induction a with
  | zero =>
      show oddPart (pow2 0 * (2 * b + 1)) = 2 * b + 1
      show oddPart (1 * (2 * b + 1)) = 2 * b + 1
      show oddPart (2 * b + 1) = 2 * b + 1
      have ho : (2 * b + 1) % 2 = 1 := by omega
      show (if (2 * b + 1) % 2 = 0 then oddPart ((2 * b + 1) / 2) else 2 * b + 1) = 2 * b + 1
      rw [if_neg (by omega)]
  | succ k ih =>
      show oddPart (pow2 (k + 1) * (2 * b + 1)) = 2 * b + 1
      show oddPart (2 * (pow2 k * (2 * b + 1))) = 2 * b + 1
      have hpos : 0 < pow2 k * (2 * b + 1) := by
        have := pow2_pos k; omega
      rw [oddPart_two_mul hpos, ih]

theorem unpair_pair (a b : Nat) : unpair (pair a b) = (a, b) := by
  show (v2 (pair a b), (oddPart (pair a b) - 1) / 2) = (a, b)
  rw [v2_pair, odd_part_pair]
  refine Prod.ext rfl ?_
  omega

theorem v2_le : ∀ n, v2 n ≤ n := by
  intro n
  refine Nat.strongRecOn n ?_
  intro m ih
  cases m with
  | zero => exact rfl
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hv : v2 (k + 1) = v2 ((k + 1) / 2) + 1 := by
          rw [e]; exact v2_two_mul (by omega)
        rw [hv]
        have := ih ((k + 1) / 2) (by omega)
        omega
      · show (if (k + 1) % 2 = 0 then v2 ((k + 1) / 2) + 1 else 0) ≤ k + 1
        rw [if_neg he]; omega

theorem oddPart_le : ∀ n, oddPart n ≤ n := by
  intro n
  refine Nat.strongRecOn n ?_
  intro m ih
  cases m with
  | zero => exact rfl
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          rw [e]; exact oddPart_two_mul (by omega)
        rw [ho]
        have := ih ((k + 1) / 2) (by omega)
        omega
      · show (if (k + 1) % 2 = 0 then oddPart ((k + 1) / 2) else k + 1) ≤ k + 1
        rw [if_neg he]

theorem oddPart_pos : ∀ {n : Nat}, n ≠ 0 → 0 < oddPart n := by
  intro n
  refine Nat.strongRecOn n ?_
  intro m ih hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          rw [e]; exact oddPart_two_mul (by omega)
        rw [ho]
        exact ih (by omega) (by omega)
      · show (if (k + 1) % 2 = 0 then oddPart ((k + 1) / 2) else k + 1) > 0
        rw [if_neg he]; omega

theorem oddPart_odd : ∀ {n : Nat}, n ≠ 0 → oddPart n % 2 = 1 := by
  intro n
  refine Nat.strongRecOn n ?_
  intro m ih hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          rw [e]; exact oddPart_two_mul (by omega)
        rw [ho]
        exact ih (by omega) (by omega)
      · show (if (k + 1) % 2 = 0 then oddPart ((k + 1) / 2) else k + 1) % 2 = 1
        rw [if_neg he]; omega

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
  refine Nat.strongRecOn n ?_
  intro m ih hm
  cases m with
  | zero => contradiction
  | succ k =>
      by_cases he : (k + 1) % 2 = 0
      · have e : k + 1 = 2 * ((k + 1) / 2) := by omega
        have hv : v2 (k + 1) = v2 ((k + 1) / 2) + 1 := by
          rw [e]; exact v2_two_mul (by omega)
        have ho : oddPart (k + 1) = oddPart ((k + 1) / 2) := by
          rw [e]; exact oddPart_two_mul (by omega)
        rw [hv, ho, ← e, mul_assoc]
        exact ih ((k + 1) / 2) (by omega) (by omega)
      · have hv : v2 (k + 1) = 0 := by
          show (if (k + 1) % 2 = 0 then v2 ((k + 1) / 2) + 1 else 0) = 0
          rw [if_neg he]
        have ho : oddPart (k + 1) = k + 1 := by
          show (if (k + 1) % 2 = 0 then oddPart ((k + 1) / 2) else k + 1) = k + 1
          rw [if_neg he]
        rw [hv, ho]
        show 1 * (k + 1) = k + 1
        rw [one_mul]

theorem pair_unpair {n : Nat} (h : n ≠ 0) : pair (unpair n).1 (unpair n).2 = n := by
  show pow2 (v2 n) * (2 * ((oddPart n - 1) / 2) + 1) = n
  have ho := oddPart_odd h
  have hp := oddPart_pos h
  have e : 2 * ((oddPart n - 1) / 2) + 1 = oddPart n := by omega
  rw [e, pow2_v2_mul_oddPart h]

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
  | n => match unpair n with
    | (0, b) => some (Term.var b)
    | (1, b) => some (Term.con b)
    | (2, b) => match unpair b with
      | (f, lr) => match unpair lr with
        | (cl, cr) => match decodeTerm cl, decodeTerm cr with
          | some l, some r => some (Term.app f l r)
          | _, _           => none
    | _ => none
termination_by decodeTerm n => n
decreasing_by
  all_goals
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    have h2 := v2_le ((oddPart (n + 1) - 1) / 2)
    have h3 := oddPart_le ((oddPart (n + 1) - 1) / 2)
    omega

theorem decodeTerm_codeTerm (t : Term) : decodeTerm (codeTerm t) = some t := by
  induction t with
  | var n =>
      show (match unpair (pair 0 n) with | (0, b) => some (Term.var b) | _ => none) = some (Term.var n)
      rw [unpair_pair]
  | con c =>
      show (match unpair (pair 1 c) with | (1, b) => some (Term.con b) | _ => none) = some (Term.con c)
      rw [unpair_pair]
  | app f l r ihl ihr =>
      show (match unpair (pair 2 (pair f (pair (codeTerm l) (codeTerm r)))) with
            | (2, b) => match unpair b with | (f, lr) => match unpair lr with
                | (cl, cr) => match decodeTerm cl, decodeTerm cr with
                    | some l, some r => some (Term.app f l r) | _, _ => none
              | _ => none | _ => none) = some (Term.app f l r)
      rw [unpair_pair, unpair_pair, unpair_pair, ihl, ihr]

/-- Sequence numbers: Gödel-coded lists of naturals (0 codes []). -/
def codeList : List Nat → Nat
  | []      => 0
  | x :: xs => pair (x + 1) (codeList xs)

def decodeList : Nat → Option (List Nat)
  | 0 => some []
  | n => match unpair n with
    | (x, r) => match decodeList r with
      | some l => some ((x - 1) :: l)
      | none   => none
termination_by decodeList n => n
decreasing_by
  all_goals
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    omega

theorem decodeList_codeList (l : List Nat) : decodeList (codeList l) = some l := by
  induction l with
  | nil    => rfl
  | cons x xs ih =>
      show (match unpair (pair (x + 1) (codeList xs)) with
            | (x', r) => match decodeList r with
              | some l => some ((x' - 1) :: l) | none => none) = some (x :: xs)
      rw [unpair_pair, ih]

inductive Goal where
  | atom (p : Nat) (args : List Nat)
  deriving DecidableEq, Repr, BEq

def codeGoal : Goal → Nat
  | Goal.atom p args => pair p (codeList args)

def decodeGoal : Nat → Option Goal
  | 0 => none
  | n => match unpair n with
    | (p, al) => match decodeList al with
      | some args => some (Goal.atom p args)
      | none      => none
termination_by decodeGoal n => n
decreasing_by
  all_goals
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    omega

theorem decodeGoal_codeGoal (g : Goal) : decodeGoal (codeGoal g) = some g := by
  cases g with
  | atom p args =>
      show (match unpair (pair p (codeList args)) with
            | (p, al) => match decodeList al with
              | some args => some (Goal.atom p args) | none => none) = some (Goal.atom p args)
      rw [unpair_pair, decodeList_codeList]

structure Rule where
  head : Goal
  body : List Goal
  deriving DecidableEq, Repr, BEq

def decodeGoals : List Nat → Option (List Goal)
  | []      => some []
  | n :: ns => match decodeGoal n, decodeGoals ns with
    | some g, some gs => some (g :: gs)
    | _, _            => none

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
termination_by decodeRule n => n
decreasing_by
  all_goals
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    have h2 := v2_le (n + 1)
    omega

theorem decodeRule_codeRule (r : Rule) : decodeRule (codeRule r) = some r := by
  cases r with
  | mk head body =>
      show (match unpair (pair (codeGoal head + 1) (codeList (body.map codeGoal))) with
            | (h, bl) => if h = 0 then none
                else match decodeGoal (h - 1), decodeList bl with
                  | some hd, some bs => match decodeGoals bs with
                      | some body => some { head := hd, body := body } | none => none
                  | _, _ => none) = some { head := head, body := body }
      rw [unpair_pair, if_neg (by omega)]
      have e : codeGoal head + 1 - 1 = codeGoal head := by omega
      rw [e, decodeGoal_codeGoal, decodeList_codeList]
      induction body with
      | nil => rfl
      | cons b bs ih =>
          show (match decodeGoal (codeGoal b), decodeGoals (List.map codeGoal bs) with
                | some g, some gs => some (g :: gs) | _, _ => none) = some (b :: bs)
          rw [decodeGoal_codeGoal, ih]

def codeProg : List Rule → Nat := codeList ∘ List.map codeRule

def decodeProg : Nat → Option (List Rule)
  | 0 => some []
  | n => match unpair n with
    | (x, r) => match decodeProg r, decodeRule x with
      | some rs, some rr => some (rr :: rs)
      | _, _ => none
termination_by decodeProg n => n
decreasing_by
  all_goals
    have h1 := unpair_snd_lt' (by omega : n + 1 ≠ 0)
    omega

theorem decodeProg_codeProg (P : List Rule) : decodeProg (codeProg P) = some P := by
  induction P with
  | nil    => rfl
  | cons r rs ih =>
      show (match unpair (pair (codeRule r + 1) (codeProg rs)) with
            | (x, r') => match decodeProg r', decodeRule x with
              | some rs, some rr => some (rr :: rs) | _, _ => none) = some (r :: rs)
      rw [unpair_pair, ih, decodeRule_codeRule]

/- ============================ Layer 2: execution =========================== -/

abbrev Prog := List Rule

/-- The machine's birth state (fixed initial database). -/
def seed : List Goal := [Goal.atom 0 [0, 1]]

/-- Element removal (keeps order); no `List.erase` API names anywhere. -/
def remove' {α : Type} [DecidableEq α] (x : α) : List α → List α
  | []     => []
  | y :: t => if y = x then remove' x t else y :: remove' x t

theorem notin_remove' {α : Type} [DecidableEq α] {x : α} (l : List α) :
    x ∉ remove' x l := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]; exact ih
      · rw [if_neg ha, List.mem_cons]
        exact ⟨ha, ih⟩

theorem remove'_sub {α : Type} [DecidableEq α] {x y : α} (l : List α) :
    y ∈ remove' x l → y ∈ l := by
  induction l with
  | nil => intro h; simp [remove'] at h
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]; intro h; right; exact ih h
      · rw [if_neg ha, List.mem_cons]
        rintro (rfl | h)
        · left; rfl
        · right; exact ih h

theorem remove'_notin {α : Type} [DecidableEq α] {x : α} {l : List α}
    (h : x ∉ l) : remove' x l = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]; simp at h
      · rw [if_neg ha, ih (fun hx => h (List.Mem.tail a hx))]

theorem length_remove' {α : Type} [DecidableEq α] {x : α} {l : List α}
    (h : x ∈ l) : (remove' x l).length = l.length - 1 := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]
        by_cases hx : x ∈ t
        · rw [ih hx]; omega
        · rw [remove'_notin hx]; omega
      · rw [if_neg ha]
        rcases h with h | h
        · simp_all
        · rw [ih h]; omega

theorem length_remove'_le {α : Type} [DecidableEq α] (x : α) (l : List α) :
    (remove' x l).length ≤ l.length := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]; omega
      · rw [if_neg ha]; omega

theorem mem_remove' {α : Type} [DecidableEq α] {x y : α} {l : List α}
    (hn : y ≠ x) : y ∈ remove' x l ↔ y ∈ l := by
  induction l with
  | nil => simp [remove']
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]
        constructor
        · intro h; right; exact ih.1 h
        · rintro (rfl | h)
          · simp_all
          · exact ih.2 h
      · rw [if_neg ha, List.mem_cons]
        constructor
        · rintro (rfl | h)
          · left; rfl
          · right; exact ih.1 h
        · rintro (rfl | h)
          · left; rfl
          · right; exact ih.2 h

theorem remove'_idem {α : Type} [DecidableEq α] (x : α) (l : List α) :
    remove' x (remove' x l) = remove' x l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases ha : a = x
      · rw [if_pos ha]; exact ih
      · show (if a = x then _ else a :: remove' x (remove' x t)) = a :: remove' x t
        rw [if_neg ha, ih]

theorem remove'_comm {α : Type} [DecidableEq α] {x y : α} (h : x ≠ y)
    (l : List α) : remove' x (remove' y l) = remove' y (remove' x l) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases hay : a = y <;> by_cases hax : a = x
      · simp_all
      · subst hay
        show remove' x (remove' y (y :: t)) = remove' y (remove' x (y :: t))
        rw [if_pos rfl, if_neg hax, if_neg (Ne.symm h), ih]
      · subst hax
        show remove' x (remove' y (x :: t)) = remove' y (remove' x (x :: t))
        rw [if_pos rfl, if_neg h, if_neg (fun e => h e.symm), ih]
      · show (if a = y then _ else a :: remove' x (remove' y t)) =
             (if a = x then _ else a :: remove' y (remove' x t))
        rw [if_neg hay, if_neg hax, ih]

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
        rw [if_pos rfl, if_pos rfl, remove'_idem, ih]
      · show remove' x (y :: remove' y (nodup' t)) = nodup' (remove' x (y :: t))
        rw [if_neg hyx, if_neg hyx, remove'_comm hyx, ih]

theorem mem_nodup' {α : Type} [DecidableEq α] (x : α) (l : List α) :
    x ∈ nodup' l ↔ x ∈ l := by
  induction l with
  | nil => simp [nodup']
  | cons y t ih =>
      show (x ∈ y :: remove' y (nodup' t)) ↔ (x = y ∨ x ∈ t)
      rw [List.mem_cons]
      constructor
      · rintro (rfl | h)
        · left; rfl
        · by_cases hxy : x = y
          · left; exact hxy
          · right; exact ih.1 (mem_remove' hxy).1 h
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
      omega

theorem remove'_append {α : Type} [DecidableEq α] {x : α} {a b : List α}
    (h : x ∉ a) : remove' x (a ++ b) = a ++ remove' x b := by
  induction a with
  | nil => rfl
  | cons y t ih =>
      have hyn : y ≠ x := fun e => h (e ▸ List.Mem.head t)
      have hxt : x ∉ t := fun hx => h (List.Mem.tail y hx)
      show (if y = x then remove' x (t ++ b) else y :: remove' x (t ++ b)) = y :: t ++ remove' x b
      rw [if_neg hyn, ih hxt]

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
      have h1 := ha
      show x :: remove' x (nodup' t) = x :: t at h1
      injection h1 with h2
      have hxn : x ∉ t := by
        intro hx
        have h3 : x ∈ nodup' t := (mem_nodup' x t).2 hx
        rw [← h2] at h3
        exact notin_remove' _ h3
      have ht : t = nodup' t := by
        have hxn' : x ∉ nodup' t := fun hx => hxn ((mem_nodup' x t).1 hx)
        rw [remove'_notin hxn'] at h2
        exact h2.symm
      obtain ⟨r, hr⟩ := ih m ht
      refine ⟨remove' x r, ?_⟩
      show x :: remove' x (nodup' (t ++ m)) = x :: t ++ remove' x r
      rw [hr, remove'_append hxn]

/-- The pigeonhole core: subsets of duplicate-free lists are no longer. -/
theorem length_le_of_subset {α : Type} [DecidableEq α] {a b : List α}
    (ha : a = nodup' a) (hb : b = nodup' b)
    (h : ∀ x ∈ a, x ∈ b) : a.length ≤ b.length := by
  induction a with
  | nil => simp
  | cons x t ih =>
      have hxn : x ∉ t := by
        have h1 := ha
        show x :: remove' x (nodup' t) = x :: t at h1
        injection h1 with h2
        intro hx
        have h3 : x ∈ nodup' t := (mem_nodup' x t).2 hx
        rw [← h2] at h3
        exact notin_remove' _ h3
      have ht : t = nodup' t := by
        have h1 := ha
        show x :: remove' x (nodup' t) = x :: t at h1
        injection h1 with h2
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
        rw [← remove'_dfl, hb]
      have hle := ih ht hb' hrem
      have hlr := length_remove' hxb
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
      intro l h
      cases l with
      | nil => simp at h
      | cons x t => exact ⟨[], x, t, rfl, rfl, rfl, rfl⟩
  | succ n ih =>
      intro l h
      cases l with
      | nil => simp at h
      | cons x t =>
          have hn : n < t.length := by simpa using h
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
  | nil => intro i x hx; simp [dropIx] at hx
  | cons y t ih =>
      intro i x hx
      cases i with
      | zero => exact List.Mem.tail y hx
      | succ n =>
          rcases hx with hx | hx
          · exact List.Mem.head _
          · exact List.Mem.tail y (ih n _ hx)

/- ---- the evaluator ----/

/-- All atoms a program can ever mention (heads plus bodies). -/
def atomsOf : Prog → List Goal
  | []      => []
  | r :: rs => r.head :: (r.body ++ atomsOf rs)

/-- Finite universe of derivable atoms: termination is data. -/
def universe_ (P : Prog) : List Goal := nodup' (seed ++ atomsOf P)

theorem universe_fix (P : Prog) : universe_ P = nodup' (universe_ P) := rfl

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
      rcases h1 with rfl | h1
      · simp only [h2, decide_false, Bool.false_and]
      · by_cases ha : a ∈ db
        · simp only [ha, decide_true, Bool.true_and]
          exact ih h1
        · simp only [ha, decide_false, Bool.false_and]

theorem memAll_true {db : List Goal} {l : List Goal}
    (h : ∀ g ∈ l, g ∈ db) : memAll db l = true := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      show (decide (a ∈ db) && memAll db t) = true
      simp only [h a (List.Mem.head t), decide_true, Bool.true_and]
      exact ih (fun g hg => h g (List.Mem.tail a hg))

theorem memAll_spec {db : List Goal} {l : List Goal}
    (h : memAll db l = true) : ∀ g ∈ l, g ∈ db := by
  induction l with
  | nil => intro g hg; simp at hg
  | cons a t ih =>
      intro g hg
      have h2 := (Bool.and_eq_true _ _).1 h
      rcases hg with hg | hg
      · exact of_decide_eq_true h2.1
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
  rcases (List.mem_append.1 hx) with hx | hx
  · exact hdb x hx
  · induction P with
    | nil => simp [List.foldr] at hx
    | cons r rs ih =>
        simp only [List.foldr] at hx
        rcases (stepAdd_mem hx) with ⟨_, rfl⟩ | hx
        · apply (mem_nodup' x (seed ++ atomsOf (r :: rs))).2
          apply List.mem_append.2; right
          show x ∈ r.head :: (r.body ++ atomsOf rs)
          exact List.Mem.head _
        · exact ih hx

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
  rcases (List.mem_append.1 hx) with hx | hx
  · exact List.mem_append.2 (Or.inl (h x hx))
  · right
    induction P with
    | nil => simp [List.foldr] at hx
    | cons r rs ih =>
        simp only [List.foldr] at hx ⊢
        by_cases ha : applicable db r = true
        · have hb := applicable_mono h r ha
          simp only [ha, hb, if_true, List.mem_cons] at hx ⊢
          rcases hx with rfl | hx
          · exact List.Mem.head _
          · right; exact ih hx
        · have hn : applicable db r = false := by
            cases hbb : applicable db r with
            | true  => simp_all
            | false => rfl
          simp only [hn, if_false] at hx
          by_cases hb : applicable db' r = true
          · simp only [hb, if_true, List.mem_cons]; right; exact ih hx
          · simp only [hb, if_false]; exact ih hx

def closure : Nat → Prog → List Goal → List Goal
  | 0,     _, db => db
  | n + 1, P, db => closure n P (closureStep P db)

theorem closure_infl (P : Prog) : ∀ fuel db, ∀ x ∈ db, x ∈ closure fuel P db := by
  intro fuel
  induction fuel with
  | zero => intro db x hx; exact hx
  | succ n ih =>
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
      apply ih
      exact closureStep_sub_universe P db h

theorem seed_fix : seed = nodup' seed := rfl

theorem closure_fixpoint (P : Prog) : ∀ fuel,
    closure fuel P seed = nodup' (closure fuel P seed) := by
  intro fuel
  cases fuel with
  | zero => exact seed_fix
  | succ n => rfl

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
      rfl

/-- Iteration splits: closure (a+b) = closure a ∘ closure b. -/
theorem closure_add : ∀ a b (P : Prog) (db : List Goal),
    closure (a + b) P db = closure a P (closure b P db) := by
  intro a
  induction a with
  | zero => intro b P db; rfl
  | succ n ih =>
      intro b P db
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
  | succ n ih =>
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
  by_contra h
  push_neg at h
  have hpre := closure_succ_append P
  have hlt : ∀ k, k < bound P →
      (closure k P seed).length < (closure (k + 1) P seed).length := by
    intro k hk
    obtain ⟨r, hr⟩ := hpre k
    have hrn : r ≠ [] := by
      intro e
      rw [e, List.append_nil] at hr
      exact h k hk hr.symm
    rw [hr]
    cases r with
    | nil => contradiction
    | cons x xs => rw [List.length_append]; omega
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
  | nil => simp only [List.foldr]; rw [h]
  | cons a t ih => simp only [List.foldr, List.cons_append, ih]

theorem closureStep_erase_dead (P : Prog) (i : Nat) (hi : i < P.length)
    (hd : ∃ g ∈ (P.get ⟨i, hi⟩).body, g ∉ outputs P)
    (db : List Goal) (hdb : ∀ x ∈ db, x ∈ outputs P) :
    closureStep P db = closureStep (dropIx P i) db := by
  obtain ⟨g, hgm, hgd⟩ := hd
  have hgnodb : g ∉ db := fun h => hgd (hdb g h)
  have hap : applicable db (P.get ⟨i, hi⟩) = false := memAll_false hgm hgnodb
  obtain ⟨l₁, r, l₂, he, hl1, hd2, hget⟩ := split_at P i hi
  subst he
  have hap' : applicable db r = false := by rw [hget]; exact hap
  show nodup' (db ++ (l₁ ++ r :: l₂).foldr (stepAdd db) []) =
       nodup' (db ++ dropIx (l₁ ++ r :: l₂) i).foldr (stepAdd db) [])
  rw [hd2]
  congr 1
  exact foldr_skip (stepAdd db) l₁ l₂ r [] (fun acc => by simp [hap'])

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
      rwa [outputs_fix P] at h1

theorem atomsOf_mono_drop (P : Prog) (i : Nat) (hi : i < P.length) :
    ∀ x ∈ atomsOf (dropIx P i), x ∈ atomsOf P := by
  induction P generalizing i with
  | nil => intro i hi x hx; simp [dropIx] at hi
  | cons r rs ih =>
      intro i hi x hx
      cases i with
      | zero => exact List.Mem.tail r.head (List.mem_append.2 (Or.inr hx))
      | succ n =>
          have hin : n < rs.length := by simpa using hi
          simp only [dropIx, atomsOf, List.mem_cons, List.mem_append] at hx ⊢
          rcases hx with rfl | h | h
          · left; rfl
          · right; left; exact h
          · right; right; exact ih n hin h

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
  ⟨outputs_erase_dead P i hi hd, length_dropIx P i hi, cost_le P i hi hd⟩

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
  | fuel + 1, P, [] => P
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
          | none => rw [hi]; exact ih P t
          | some P' =>
            rw [hi]
            obtain ⟨h1, h2⟩ := ih P' t
            obtain ⟨ho, hl, _⟩ := install_improves P P' c hi
            exact ⟨Nat.le_trans h1 hl, by rw [h2, ho]⟩

/- ================================== demo ==================================== -/

def prog0 : Prog := [ ⟨Goal.atom 1 [0, 1], [Goal.atom 0 [0, 1]]⟩,
                      ⟨Goal.atom 2 [0],     [Goal.atom 9 [0]]⟩ ]

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
