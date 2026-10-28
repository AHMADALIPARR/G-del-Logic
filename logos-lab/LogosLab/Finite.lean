/-
  LogosLab.Finite — finiteness by construction, as an explicit
  enumeration. See MEASURES.md §5.

  Lean 4.12 core has no Finite/Fintype class, so this project does
  NOT appeal to one. Finiteness here means: an explicit list that
  enumerates every object in the set. The finiteness THEOREM for
  explanations (exhibiting the index injection and proving the
  enumeration covers it) is FUTURE and blocked — see STATUS.md.
  What exists now is the enumeration function itself, which is
  the construction the theorem will be about.
-/

namespace LogosLab

/-- Finiteness as an explicit enumeration list. Every element of α
    must occur in the list; duplicates are allowed. -/
def FiniteEnum (α : Type) : Prop :=
  ∃ l : List α, ∀ a : α, a ∈ l

/-- Enumerate every `Fin k`, in order. -/
def allFin : (k : Nat) -> List (Fin k)
  | 0 => []
  | k + 1 => (allFin k).map Fin.castSucc ++ [Fin.last k]

/-- Enumerate every list over `Fin k` of length ≤ d, by recursion
    on d. The previous level is kept, and every list of the previous
    level is extended by every `Fin k`. Duplicates may occur; that
    does not affect enumeration (see `FiniteEnum`). -/
def boundedLists : (k d : Nat) -> List (List (Fin k))
  | _, 0 => [[]]
  | k, d + 1 =>
      let prev := boundedLists k d
      prev ++ prev.foldr (fun l acc => (allFin k).map (fun x => l ++ [x]) ++ acc) []

/-- A bounded explanation encoding: a list of abducible indices
    (indices into a fixed abducible list of length k), with length
    at most d. The explanation itself is recovered by mapping indices
    through the abducible list; that recovery function and the
    finiteness theorem are solver-phase work. -/
abbrev BoundedExplanation (k d : Nat) :=
  { l : List (Fin k) // l.length ≤ d }

end LogosLab
