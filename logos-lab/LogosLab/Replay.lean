-- SPDX-License-Identifier: AGPL-3.0-only OR LicenseRef-SnapKitty-Opaque-1.0
-- Copyright Ahmad Ali Parr
/-
  LogosLab.Replay — syntactic soundness: every answer returned by
  `solve` has a `Deriv` tree (theorem 1, `replay_sound`), and every
  candidate accepted by the kernel `checker` has a `Deriv` tree
  (theorem 2, `checker_sound`).

  These are syntactic replay theorems: a derivation is built by
  following the exact steps the solver / trace took, using the
  unify equations those steps already produced. They do not depend
  on the semantic lemma `unify_sound` (applied atoms equal under
  the final substitution), which remains blocked in STATUS.md.
  That separation is deliberate and stated here, not hidden.
-/

import LogosLab.Deriv

namespace LogosLab

/-- Membership in `flattenAnswers`: an answer is in the flattening
    iff it is in some component list. -/
theorem mem_flattenAnswers {ls : List (List Answer)} {ans : Answer} :
    ans ∈ flattenAnswers ls ↔ ∃ l ∈ ls, ans ∈ l := by
  induction ls with
  | nil => simp [flattenAnswers]
  | cons l rest ih =>
      have hflat : flattenAnswers (l :: rest) = l ++ flattenAnswers rest := rfl
      rw [hflat, List.mem_append, ih]
      constructor
      · intro h
        rcases h with h | h
        · exact ⟨l, List.mem_cons_self l rest, h⟩
        · obtain ⟨l', hl', ha⟩ := h
          exact ⟨l', List.mem_cons_of_mem l hl', ha⟩
      · intro h
        obtain ⟨l', hl', ha⟩ := h
        rw [List.mem_cons] at hl'
        rcases hl' with rfl | hl''
        · exact Or.inl ha
        · exact Or.inr ⟨l', hl'', ha⟩

/-- A successor from `successorsFromChoices` comes from some choice
    in the choice list, with matching goals, substitution, depth,
    cut barrier, and with the parent's accumulated explanation. -/
theorem successorsFromChoices_mem {st : State} {cs : List Alternative}
    {s' : State} (h : s' ∈ successorsFromChoices st cs) :
    ∃ c ∈ cs, s'.goals = c.goals ∧ s'.subst = c.subst ∧
      s'.depth = c.depth ∧ s'.cutBarrier = c.cutBarrier ∧
      s'.abduced = st.abduced := by
  induction cs with
  | nil => simp [successorsFromChoices] at h
  | cons c rest ih =>
      simp only [successorsFromChoices, List.mem_cons] at h
      rcases h with h | h
      · -- head successor: it is exactly the record built from c
        subst h
        exact ⟨c, List.mem_cons_self c rest, rfl, rfl, rfl, rfl, rfl⟩
      · obtain ⟨c', hc', hg, hs, hd, hb, ha⟩ := ih h
        exact ⟨c', List.mem_cons_of_mem c hc', hg, hs, hd, hb, ha⟩

/-- A choice from `clauseChoices` comes from some clause in the
    program, unified with the head atom, with matching goals. -/
theorem clauseChoices_mem {prog : Program} {st : State} {a : Atom}
    {rs : List Goal} {alt : Alternative}
    (h : alt ∈ clauseChoices prog st a rs) :
    ∃ cl ∈ prog, unifyAtom st.subst cl.head a = some alt.subst ∧
      alt.goals = cl.body ++ rs := by
  unfold clauseChoices at h
  rw [List.mem_filterMap] at h
  obtain ⟨cl, hcl, hmap⟩ := h
  -- hmap : (unifyAtom ...).map (fun s' => {...}) = some alt
  cases hunify : unifyAtom st.subst cl.head a with
  | none => simp [hunify] at hmap
  | some s' =>
      simp only [hunify, Option.map_some'] at hmap
      have hrecord := Option.some.inj hmap
      subst hrecord
      exact ⟨cl, hcl, hunify, rfl⟩

/-- A `step` successor for an atom goal comes from some clause in
    the program, unified with the head atom, with matching goals
    and the parent's accumulated explanation. -/
theorem step_mem_atom {prog : Program} {st : State} {a : Atom}
    {rs : List Goal} {s' : State}
    (hgoals : st.goals = Goal.atom a :: rs)
    (h : s' ∈ step prog st) :
    ∃ cl ∈ prog, unifyAtom st.subst cl.head a = some s'.subst ∧
      s'.goals = cl.body ++ rs ∧ s'.abduced = st.abduced := by
  -- Unfold step on the atom goal.
  have hstep : step prog st = successorsFromChoices st (clauseChoices prog st a rs) := by
    unfold step
    rw [hgoals]
  rw [hstep] at h
  obtain ⟨c, hc, hg, hs, _hd, _hb, ha⟩ := successorsFromChoices_mem h
  obtain ⟨cl, hcl, hunify, hgoals'⟩ := clauseChoices_mem hc
  -- c.subst = alt.subst from clauseChoices, and s'.subst = c.subst
  refine ⟨cl, hcl, ?_, ?_, ha⟩
  · rw [hs]; exact hunify
  · rw [hg, hgoals']


/-- Theorem 1, `replay_sound`: every answer returned by `solve`
    has a `Deriv` tree for the initial state. Proof by induction
    on fuel, generalising over the state and answer. -/
theorem replay_sound : ∀ (fuel : Nat) (prog : Program) (A : List Atom)
    (guard : Guard) (st : State) (ans : Answer),
    ans ∈ solve fuel prog A guard st ->
    Deriv prog A st.goals st.subst st.abduced ans.abduced ans.subst := by
  intro fuel
  induction fuel with
  | zero =>
      intro prog A guard st ans h
      simp [solve] at h
  | succ fuel ih =>
      intro prog A guard st ans h
      obtain ⟨goals, subst, depth, barrier, alts, abduced⟩ := st
      -- The state is now the record built from these fields.
      by_cases hg : guard { goals := goals, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced }
      · cases goals with
        | nil =>
            simp only [solve, hg] at h
            simp only [↓reduceIte, List.mem_singleton] at h
            subst h
            exact Deriv.empty subst abduced
        | cons g rs =>
            cases g with
            | cut =>
                simp only [solve, hg] at h
                -- h : ans ∈ solve fuel prog A guard (cutStep ... rs)
                have hd := ih prog A guard
                  (cutStep { goals := Goal.cut :: rs, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced } rs) ans h
                -- cutStep preserves subst and abduced, and sets goals to rs
                exact Deriv.cut rs subst abduced ans.abduced ans.subst hd
            | atom a =>
                simp only [solve, hg] at h
                simp only [↓reduceIte] at h
                rw [List.mem_append] at h
                rcases h with hclause | habduce
                · -- Clause answers
                  obtain ⟨l, hl, ha⟩ := (mem_flattenAnswers).mp hclause
                  rw [List.mem_map] at hl
                  obtain ⟨s', hs', hl'⟩ := hl
                  cases hgs : guard s'
                  · simp [hgs] at hl'
                    subst hl'
                    simp at ha
                  · -- ans ∈ solve fuel ... s'
                    simp [hgs] at hl'
                    subst hl'
                    have hd := ih prog A guard s' ans ha
                    obtain ⟨cl, hcl, hunify, hgoals', habd⟩ :=
                      step_mem_atom (st := { goals := Goal.atom a :: rs, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced }) rfl hs'
                    rw [hgoals', habd] at hd
                    exact Deriv.resolve a rs subst s'.subst abduced ans.abduced ans.subst
                      cl hcl hunify hd
                · -- Abduce answers
                  by_cases ha_mem : a ∈ A
                  · rw [if_pos ha_mem] at habduce
                    cases hguard : guard (abduceState { goals := Goal.atom a :: rs, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced } a rs)
                    · simp [hguard] at habduce
                    · simp only [hguard, ↓reduceIte] at habduce
                      have hd := ih prog A guard (abduceState { goals := Goal.atom a :: rs, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced } a rs) ans habduce
                      exact Deriv.abduce a rs subst abduced ans.abduced ans.subst ha_mem hd
                  · rw [if_neg ha_mem] at habduce
                    simp at habduce
      · -- guard false: solve returns []
        have hnil : solve (fuel + 1) prog A guard
            { goals := goals, subst := subst, depth := depth, cutBarrier := barrier, alternatives := alts, abduced := abduced } = [] := by
          simp [solve, hg]
        rw [hnil] at h
        simp at h


/-- Trace replay is sound: if a trace replays to a final
    explanation and substitution, then a `Deriv` tree exists for
    the initial goals with exactly those finals. Proof by
    induction on the trace, generalising over goals, substitution,
    and accumulated explanation. -/
theorem replayTrace_sound : ∀ (trace : List TraceStep) (prog : Program)
    (A : List Atom) (goals : List Goal) (s : Subst) (Δ Δf : List Atom)
    (sf : Subst),
    replayTrace prog A goals s Δ trace = some (Δf, sf) ->
    Deriv prog A goals s Δ Δf sf := by
  intro trace
  induction trace with
  | nil =>
      intro prog A goals s Δ Δf sf h
      cases goals with
      | nil =>
          simp only [replayTrace] at h
          have hpair : (Δ, s) = (Δf, sf) := Option.some.inj h
          have hΔ : Δ = Δf := congrArg Prod.fst hpair
          have hsf : s = sf := congrArg Prod.snd hpair
          subst hΔ
          subst hsf
          exact Deriv.empty s Δ
      | cons g rs => simp [replayTrace] at h
  | cons step rest ih =>
      intro prog A goals s Δ Δf sf h
      cases goals with
      | nil => simp [replayTrace] at h
      | cons g rs =>
          cases g with
          | cut =>
              cases step with
              | cut =>
                  simp only [replayTrace] at h
                  have hd := ih prog A rs s Δ Δf sf h
                  exact Deriv.cut rs s Δ Δf sf hd
              | resolve _ => simp [replayTrace] at h
              | abduce _ => simp [replayTrace] at h
          | atom a =>
              cases step with
              | resolve i =>
                  cases hget : prog[i]? with
                  | none => simp [replayTrace, hget] at h
                  | some cl =>
                      cases hunify : unifyAtom s cl.head a with
                      | none => simp [replayTrace, hget, hunify] at h
                      | some s' =>
                          simp only [replayTrace, hget, hunify] at h
                          have hd := ih prog A (cl.body ++ rs) s' Δ Δf sf h
                          have hcl : cl ∈ prog := List.getElem?_mem hget
                          exact Deriv.resolve a rs s s' Δ Δf sf cl hcl hunify hd
              | abduce b =>
                  by_cases hab : a = b ∧ b ∈ A
                  · simp only [replayTrace, hab, ↓reduceIte] at h
                    obtain ⟨hab_eq, hab_mem⟩ := hab
                    subst hab_eq
                    have hd := ih prog A rs s (a :: Δ) Δf sf h
                    exact Deriv.abduce a rs s Δ Δf sf hab_mem hd
                  · simp [replayTrace, hab] at h
              | cut => simp [replayTrace] at h

/-- Theorem 2, `checker_sound`: if the kernel checker accepts an
    external candidate (by replaying its trace), then a `Deriv`
    tree exists for that candidate. Trust base = kernel only: the
    trace is untrusted input, acceptance is by replay. -/
theorem checker_sound : ∀ (prog : Program) (A : List Atom)
    (goals : List Goal) (s : Subst) (Δ : List Atom) (ans : Answer)
    (trace : List TraceStep),
    checker prog A goals s Δ ans trace = true ->
    Deriv prog A goals s Δ ans.abduced ans.subst := by
  intro prog A goals s Δ ans trace h
  unfold checker at h
  cases hrep : replayTrace prog A goals s Δ trace with
  | none => simp [hrep] at h
  | some pair =>
      obtain ⟨Δf, sf⟩ := pair
      simp only [hrep] at h
      rw [Bool.and_eq_true] at h
      obtain ⟨h1, h2⟩ := h
      have hΔ : Δf = ans.abduced := of_decide_eq_true h1
      have hsf : sf = ans.subst := of_decide_eq_true h2
      subst hΔ
      subst hsf
      exact replayTrace_sound trace prog A goals s Δ ans.abduced ans.subst hrep

/-- `solve_terminates` as specified: with fuel 0, `solve` returns
    no answers, by definition. -/
theorem solve_terminates : ∀ (fuel : Nat) (prog : Program) (A : List Atom)
    (guard : Guard) (st : State),
    fuel = 0 -> solve fuel prog A guard st = [] := by
  intro fuel prog A guard st hf
  subst hf
  rfl

end LogosLab
