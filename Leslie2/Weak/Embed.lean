/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Weak.WeakChar

/-!
# Embedding weak transitions along an injective, step-preserving state map

The reusable primitive behind the parallel/interleave precongruence lift lemmas. Given an
**injective** state embedding `ι : State → State'` between two systems that **preserves steps**
(`sys.step s l μ → sys'.step (ι s) l (μ.map ι)`), a weak transition of `sys` transports to the
`ι`-pushforward weak transition of `sys'`:

* `hyperStep_embed` — a single hyper-step transports (purely structural: the convex kernel is
  pushed through `ι`);
* `weakTau_embed` — a τ-closure transports (the genuine crux: the witnessing `WeakScheduler` is
  mapped along `ι`, emitting `⊥` off the `ι`-image so the *global* `valid`/`internal_only`
  obligations stay clean, and its halting distribution pushes forward to `ν.map ι`);
* `weakStep_embed` — a weak `l`-step transports (the three layers via `weakTau_embed` twice and
  `hyperStep_embed` once).

Unlike the abstraction lifts (`weakTau_mono`, same state space, scheduler reused verbatim), here the
state space changes, so `weakTau_embed` genuinely maps the scheduler along `ι`. The binary
`parallel` lifts use `ι = (·, s_B)`; the finite `interleave` lifts use `ι = Function.update s i ·`
(both injective). The `μ.map ι` shapes reduce to `prodPMF`/`piPMF` via `prodPMF_pure_right` /
`piPMF_update_pure` at the call sites.
-/

open Stream'

namespace PLTS

variable {State State' Label : Type} [Silent Label]

omit [Silent Label] in
/-- **Embedding a hyper-step.** Purely structural: push the convex kernel `p` through `ι`. The
per-state kernel on `State'` reads back the (unique) `ι`-preimage via `Function.invFun ι`; off the
`ι`-image it is junk but unreached from `μ.map ι`. -/
theorem hyperStep_embed {sys : System State Label} {sys' : System State' Label}
    (ι : State → State') (hι : Function.Injective ι) {l : Label}
    (hstep : ∀ s μ, sys.step s l μ → sys'.step (ι s) l (μ.map ι))
    {μ ν : PMF State} (h : hyperStep sys μ l ν) :
    hyperStep sys' (μ.map ι) l (ν.map ι) := by
  classical
  obtain ⟨p, hp, hν⟩ := h
  refine ⟨fun s' => if hs' : ∃ s, ι s = s' then (p hs'.choose).map (fun m => m.map ι)
      else PMF.pure (PMF.pure s'), ?_, ?_⟩
  · -- validity of the pushed kernel
    intro s' hs'mem m' hm'mem
    rw [PMF.mem_support_map_iff] at hs'mem
    obtain ⟨s, hsmem, hιs⟩ := hs'mem
    have hex : ∃ t, ι t = s' := ⟨s, hιs⟩
    have hchoose : hex.choose = s := hι (hex.choose_spec.trans hιs.symm)
    -- `m'` is `m.map ι` for some `m ∈ (p s).support`
    simp only at hm'mem
    have hdite : (if hs' : ∃ t, ι t = s' then (p hs'.choose).map (fun m => m.map ι)
        else PMF.pure (PMF.pure s')) = (p s).map (fun m => m.map ι) := by
      rw [dif_pos hex, hchoose]
    rw [hdite, PMF.mem_support_map_iff] at hm'mem
    obtain ⟨m, hmmem, hm'⟩ := hm'mem
    subst hm'
    subst hιs
    exact hstep s m (hp s hsmem m hmmem)
  · -- the bind equality
    rw [hν]
    -- LHS: (μ.bind (fun s => (p s).bind id)).map ι
    -- reduce both sides to `μ.bind (fun s => (p s).bind (fun m => m.map ι))`
    rw [PMF.map_bind]
    rw [PMF.bind_map]
    congr 1
    funext s
    have hex : ∃ t, ι t = ι s := ⟨s, rfl⟩
    have hchoose : hex.choose = s := hι hex.choose_spec
    simp only [Function.comp_apply, dif_pos hex, hchoose, PMF.map_bind, PMF.bind_map]
    rfl

/-! ### Helpers for `weakTau_embed`

The witnessing `WeakScheduler` is mapped along `ι` via `embedSched`, emitting the `ι`-pushforward
of the original emission on the `ι`-image and halting (`⊥`) off it. The section variable
`[Nonempty State]` (extracted from `μ` at the use site) makes `Function.invFun ι` available for the
image guard. -/

/-- The one-step emission pushed along `ι`: `some (l, m) ↦ some (l, m.map ι)`, `none ↦ none`. -/
noncomputable def embedEmit (ι : State → State') :
    Option (Label × PMF State) → Option (Label × PMF State') :=
  fun o => o.map (fun x => (x.1, x.2.map ι))

/-- `Seq.ofList` of a list with one element appended is `append` of a singleton `cons`. -/
private theorem ofList_append_singleton {γ : Type} (L : List γ) (x : γ) :
    Stream'.Seq.ofList (L ++ [x]) = (Stream'.Seq.ofList L).append (Seq.cons x Seq.nil) := by
  induction L with
  | nil => simp [Stream'.Seq.ofList_nil, Stream'.Seq.nil_append, Stream'.Seq.ofList_cons]
  | cons a t ih =>
    rw [List.cons_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_cons,
      Stream'.Seq.cons_append, ih]

omit [Silent Label] in
/-- Inverting `embedEmit`: a pushed emission `some (l, μ')` comes from `some (l, m)` with
`μ' = m.map ι`. -/
private theorem embedEmit_some {ι : State → State'} {o : Option (Label × PMF State)}
    {l : Label} {μ' : PMF State'} (h : embedEmit ι o = some (l, μ')) :
    ∃ m : PMF State, o = some (l, m) ∧ μ' = m.map ι := by
  cases o with
  | none => simp [embedEmit] at h
  | some x =>
    obtain ⟨l₀, m₀⟩ := x
    simp only [embedEmit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    exact ⟨m₀, by rw [h.1], h.2.symm⟩

omit [Silent Label] in
/-- `embedEmit` preserves the halting (`none`) mass. -/
private theorem embedEmit_map_none {ι : State → State'} (q : PMF (Option (Label × PMF State))) :
    (q.map (embedEmit ι)) none = q none := by
  classical
  rw [PMF.map_apply, tsum_eq_single none (fun o ho => ?_)]
  · simp [embedEmit]
  · cases o with
    | none => simp at ho
    | some x => simp [embedEmit]

omit [Silent Label] in
/-- `stateAt` commutes with `AlterSeq.map`. -/
private theorem AlterSeq.mapFib_stateAt {X Y : Type} (f : X → Y) (e : AlterSeq X Label) (n : ℕ) :
    (e.map f).stateAt n = (e.stateAt n).map f := by
  cases n with
  | zero => rfl
  | succ k =>
    change ((e.trans.map (fun lq => (lq.1, f lq.2))).get? k).map Prod.snd
      = ((e.trans.get? k).map Prod.snd).map f
    rw [Stream'.Seq.map_get?]
    cases e.trans.get? k with
    | none => rfl
    | some lq => rfl

omit [Silent Label] in
/-- `AlterSeq.map` preserves `TerminatedAt`. -/
private theorem AlterSeq.map_terminatedAt {X Y : Type} (f : X → Y) (e : AlterSeq X Label)
    (n : ℕ) : (e.map f).trans.TerminatedAt n ↔ e.trans.TerminatedAt n := by
  change (e.trans.map (fun lq => (lq.1, f lq.2))).TerminatedAt n ↔ _
  unfold Stream'.Seq.TerminatedAt
  rw [Stream'.Seq.map_get?]; simp [Option.map_eq_none_iff]

omit [Silent Label] in
/-- `AlterSeq.map` is functorial: `(e.map f).map g = e.map (g ∘ f)`. -/
private theorem AlterSeq.map_map {X Y Z : Type} (f : X → Y) (g : Y → Z) (e : AlterSeq X Label) :
    (e.map f).map g = e.map (g ∘ f) := by
  unfold AlterSeq.map; simp only [AlterSeq.mk.injEq, Function.comp_apply, true_and]
  rw [← Stream'.Seq.map_comp]; rfl

omit [Silent Label] in
/-- `AlterSeq.map id` is the identity. -/
private theorem AlterSeq.map_id {X : Type} (e : AlterSeq X Label) : e.map id = e := by
  unfold AlterSeq.map; cases e; simp only [id_eq, AlterSeq.mk.injEq, true_and]
  exact Stream'.Seq.map_id _

omit [Silent Label] in
/-- `AlterSeq.map` commutes with `endState`: projecting an execution then taking its end-state
equals projecting the end-state. -/
private theorem AlterSeq.map_endState {X Y : Type} (f : X → Y) (e : AlterSeq X Label)
    (h : e.trans.Terminates) :
    (e.map f).endState ((AlterSeq.map_trans_terminates_iff f e).mpr h) = f (e.endState h) := by
  rw [AlterSeq.endState_eq_getLast?, AlterSeq.endState_eq_getLast?]
  have h_toList : (e.map f).trans.toList ((AlterSeq.map_trans_terminates_iff f e).mpr h)
      = (e.trans.toList h).map (fun lq => (lq.1, f lq.2)) := by
    change (e.trans.map (fun lq => (lq.1, f lq.2))).toList _ = _
    apply Stream'.Seq.ofList_injective
    rw [Stream'.Seq.ofList_toList _ _, ← Stream'.Seq.map_ofList_pub, Stream'.Seq.ofList_toList _ h]
  rw [h_toList, List.getLast?_map]
  cases (e.trans.toList h).getLast? with
  | none => rfl
  | some lq => rfl

section EmbedNonempty

variable [Nonempty State]

omit [Silent Label] in
/-- Under injectivity, `map (invFun ι)` left-inverts `map ι` on `AlterSeq`. -/
private theorem AlterSeq.map_invFun_map {ι : State → State'} (hι : Function.Injective ι)
    (e : AlterSeq State Label) : (e.map ι).map (Function.invFun ι) = e := by
  rw [AlterSeq.map_map,
    show (Function.invFun ι ∘ ι) = id from funext (Function.leftInverse_invFun hι)]
  exact AlterSeq.map_id e

open Classical in
/-- **The mapped weak scheduler.** On an execution that is the `ι`-image of a `sys`-execution
(detected by the guard `map ι (map (invFun ι) e') = e'`) it re-emits the `ι`-pushforward of the
original emission; off the image it halts (`⊥`). -/
noncomputable def embedSched {sys : System State Label} {sys' : System State' Label}
    {ι : State → State'} (_hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    (σ : WeakScheduler sys) : WeakScheduler sys' where
  next e' :=
    if (AlterSeq.map ι (AlterSeq.map (Function.invFun ι) e')) = e'
    then (σ.next (AlterSeq.map (Function.invFun ι) e')).map (embedEmit ι)
    else PMF.pure none
  valid := by
    intro e' n s' h_term h_state l μ' hsupp
    classical
    by_cases hc : (AlterSeq.map ι (AlterSeq.map (Function.invFun ι) e')) = e'
    · set pre := AlterSeq.map (Function.invFun ι) e' with hpre
      rw [if_pos hc, PMF.mem_support_map_iff] at hsupp
      obtain ⟨o, ho, hoeq⟩ := hsupp
      obtain ⟨m, hm, hμ'⟩ := embedEmit_some hoeq
      subst hm
      have hstate' : (pre.map ι).stateAt n = (pre.stateAt n).map ι :=
        AlterSeq.mapFib_stateAt ι pre n
      rw [hc, h_state] at hstate'
      obtain ⟨s₀, hs₀, hs'eq⟩ : ∃ s₀, pre.stateAt n = some s₀ ∧ ι s₀ = s' := by
        cases hpn : pre.stateAt n with
        | none => rw [hpn] at hstate'; simp at hstate'
        | some s₀ =>
          rw [hpn] at hstate'; simp only [Option.map_some, Option.some.injEq] at hstate'
          exact ⟨s₀, rfl, hstate'.symm⟩
      have hpre_term : pre.trans.TerminatedAt n := by
        rw [← AlterSeq.map_terminatedAt ι pre n, hc]; exact h_term
      have hstep_pre : sys.step s₀ l m := σ.valid pre n s₀ hpre_term hs₀ l m ho
      have hl : l = Silent.τ := σ.internal_only pre l m ho
      subst hl
      rw [hμ', ← hs'eq]
      exact hstep s₀ m hstep_pre
    · rw [if_neg hc] at hsupp; simp at hsupp
  internal_only := by
    intro e' l μ' hsupp
    classical
    by_cases hc : (AlterSeq.map ι (AlterSeq.map (Function.invFun ι) e')) = e'
    · rw [if_pos hc, PMF.mem_support_map_iff] at hsupp
      obtain ⟨o, ho, hoeq⟩ := hsupp
      obtain ⟨m, hm, hμ'⟩ := embedEmit_some hoeq
      subst hm
      exact σ.internal_only _ l m ho
    · rw [if_neg hc] at hsupp; simp at hsupp

/-- On the `ι`-image of a `sys`-execution the mapped scheduler re-emits the pushforward of the
original emission. -/
private theorem embedSched_next_image {sys : System State Label} {sys' : System State' Label}
    {ι : State → State'} (hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    (σ : WeakScheduler sys) (E : AlterSeq State Label) :
    (embedSched hι hstep σ).next (E.map ι)
      = (σ.next E).map (embedEmit ι) := by
  classical
  have hinv : AlterSeq.map (Function.invFun ι) (E.map ι) = E :=
    AlterSeq.map_invFun_map hι E
  change (if (AlterSeq.map ι (AlterSeq.map (Function.invFun ι) (E.map ι))) = E.map ι
      then (σ.next (AlterSeq.map (Function.invFun ι) (E.map ι))).map (embedEmit ι)
      else PMF.pure none) = _
  rw [hinv, if_pos rfl]

omit [Silent Label] [Nonempty State] in
/-- **The one-step kernel matches under the embedding.** On a `sys`-execution prefix `E`, the mapped
scheduler's kernel at `(l, ι s)` from `μ.map ι` equals the original kernel at `(l, s)` from `μ`. -/
private theorem embedSched_kernel
    {ι : State → State'} (hι : Function.Injective ι)
    (q : PMF (Option (Label × PMF State))) (l : Label) (s : State) :
    (∑' m' : PMF State', (q.map (embedEmit ι)) (some (l, m')) * m' (ι s))
      = ∑' m : PMF State, q (some (l, m)) * m s := by
  classical
  set G : PMF State' → ENNReal :=
    fun m' => (q.map (embedEmit ι)) (some (l, m')) * m' (ι s) with hG
  have hsupp : Function.support G ⊆ Set.range (PMF.map ι) := by
    intro m' hm'
    simp only [Function.mem_support, hG] at hm'
    have h1 : (q.map (embedEmit ι)) (some (l, m')) ≠ 0 := fun h => hm' (by rw [h, zero_mul])
    rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at h1
    obtain ⟨o, _, hoeq⟩ := h1
    obtain ⟨m, _, hμ'⟩ := embedEmit_some hoeq
    exact ⟨m, hμ'.symm⟩
  rw [← Function.Injective.tsum_eq (PMF.map_injective hι) hsupp]
  refine tsum_congr (fun m => ?_)
  rw [hG]; simp only
  rw [show (PMF.map ι m) (ι s) = m s from by
    rw [PMF.map_apply, tsum_eq_single s (fun b hb => if_neg (fun h => hb (hι h).symm)), if_pos rfl]]
  congr 1
  rw [PMF.map_apply, tsum_eq_single (some (l, m)) (fun o ho => ?_)]
  · simp only [embedEmit, Option.map_some, if_pos]
  · rw [if_neg (fun heq => ?_)]
    cases o with
    | none => simp [embedEmit] at heq
    | some x =>
      obtain ⟨l₀, m₀⟩ := x
      simp only [embedEmit, Option.map_some, Option.some.injEq, Prod.mk.injEq] at heq
      exact ho (by rw [heq.1, PMF.map_injective hι heq.2.symm])

/-- **The one-step kernel transports under the embedding.** The mapped execution's kernel at
`(l, ι s')` from `μ.map ι` equals the original kernel at `(l, s')` from `μ`, on any `sys`-execution
prefix `E`. -/
private theorem embedSched_kernel_transport {sys : System State Label} {sys' : System State' Label}
    {ι : State → State'} (hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    (σ : WeakScheduler sys) (μ : PMF State) (E : AlterSeq State Label) (l : Label) (s' : State) :
    (⟨(μ.map ι), (embedSched hι hstep σ).toScheduler⟩
        : ProbabilisticExecution sys').kernel (E.map ι) (l, ι s')
      = (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).kernel E (l, s') := by
  change (∑' m', (embedSched hι hstep σ).next (E.map ι) (some (l, m')) * m' (ι s'))
    = ∑' m, σ.next E (some (l, m)) * m s'
  rw [embedSched_next_image hι hstep σ E, embedSched_kernel hι (σ.next E) l s']

/-- **`probOf` transports under the embedding.** For a `sys`-execution `⟨s₀, ofList L⟩`, the
probability of its `ι`-image under `⟨μ.map ι, embedSched⟩` equals the probability of the original
under `⟨μ, σ⟩`. Proven by cons-end induction on the transition list `L`. -/
private theorem embedSched_probOf {sys : System State Label} {sys' : System State' Label}
    {ι : State → State'} (hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    (σ : WeakScheduler sys) (μ : PMF State) (s₀ : State) (L : List (Label × State))
    (hFin : (Stream'.Seq.ofList L : Seq (Label × State)).Terminates)
    (hFin' : ((⟨s₀, Stream'.Seq.ofList L⟩ : AlterSeq State Label).map ι).trans.Terminates) :
    (⟨(μ.map ι), (embedSched hι hstep σ).toScheduler⟩ : ProbabilisticExecution sys').probOf
        ((⟨s₀, Stream'.Seq.ofList L⟩ : AlterSeq State Label).map ι) hFin'
      = (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
          ⟨s₀, Stream'.Seq.ofList L⟩ hFin := by
  classical
  set peC : ProbabilisticExecution sys' := ⟨μ.map ι, (embedSched hι hstep σ).toScheduler⟩ with hpeC
  set peA : ProbabilisticExecution sys := ⟨μ, σ.toScheduler⟩ with hpeA
  -- `map ι` of a `ofList` execution is again a `ofList` execution (mapped list).
  have hmapForm : ∀ (LL : List (Label × State)),
      (⟨s₀, Stream'.Seq.ofList LL⟩ : AlterSeq State Label).map ι
        = ⟨ι s₀, Stream'.Seq.ofList (LL.map (fun lq => (lq.1, ι lq.2)))⟩ := by
    intro LL
    unfold AlterSeq.map
    simp only [AlterSeq.mk.injEq, true_and]
    rw [← Stream'.Seq.map_ofList_pub]
  -- move to canonical termination proofs, then induct on `L`
  revert hFin hFin'
  induction L using List.reverseRecOn with
  | nil =>
    intro hFin hFin'
    rw [ProbabilisticExecution.probOf_congr peC _ ⟨ι s₀, Seq.nil⟩ (by rw [hmapForm]; rfl) hFin'
      Stream'.Seq.terminates_nil]
    rw [ProbabilisticExecution.probOf_congr peA _ ⟨s₀, Seq.nil⟩ (by rw [Stream'.Seq.ofList_nil])
      hFin Stream'.Seq.terminates_nil]
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.probOf_nil,
      ProbabilisticExecution.init_eq_initState, ProbabilisticExecution.init_eq_initState,
      hpeC, hpeA]
    change (μ.map ι) (ι s₀) = μ s₀
    rw [PMF.map_apply, tsum_eq_single s₀ (fun b hb => if_neg (fun h => hb (hι h).symm)), if_pos rfl]
  | append_singleton L' last ih =>
    intro hFin hFin'
    obtain ⟨l, s'⟩ := last
    -- RHS: probOf ⟨s₀, ofList (L' ++ [(l,s')])⟩ = probOf ⟨s₀, ofList L'⟩ * kernel ...
    have hRHS_eq : (⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ : AlterSeq State Label)
        = ⟨s₀, (Stream'.Seq.ofList L').append (Seq.cons (l, s') Seq.nil)⟩ := by
      rw [ofList_append_singleton]
    rw [ProbabilisticExecution.probOf_congr peA _
      ⟨s₀, (Stream'.Seq.ofList L').append (Seq.cons (l, s') Seq.nil)⟩ hRHS_eq hFin
      (hRHS_eq ▸ hFin)]
    rw [ProbabilisticExecution.probOf_append_singleton peA s₀ (Stream'.Seq.ofList L')
      (Stream'.Seq.terminates_ofList L') (l, s') _]
    -- LHS: rewrite mapped exec into ofList of the mapped list, then split the last transition
    have hLHS_form : (⟨s₀, Stream'.Seq.ofList (L' ++ [(l, s')])⟩ : AlterSeq State Label).map ι
        = ⟨ι s₀, (Stream'.Seq.ofList (L'.map (fun lq => (lq.1, ι lq.2)))).append
            (Seq.cons (l, ι s') Seq.nil)⟩ := by
      rw [hmapForm, List.map_append, List.map_cons, List.map_nil, ofList_append_singleton]
    rw [ProbabilisticExecution.probOf_congr peC _
      ⟨ι s₀, (Stream'.Seq.ofList (L'.map (fun lq => (lq.1, ι lq.2)))).append
        (Seq.cons (l, ι s') Seq.nil)⟩ hLHS_form hFin' (hLHS_form ▸ hFin')]
    rw [ProbabilisticExecution.probOf_append_singleton peC (ι s₀)
      (Stream'.Seq.ofList (L'.map (fun lq => (lq.1, ι lq.2))))
      (Stream'.Seq.terminates_ofList _) (l, ι s') _]
    -- the mapped prefix is `(⟨s₀, ofList L'⟩).map ι`
    have hmapL' : (⟨ι s₀, Stream'.Seq.ofList (L'.map (fun lq => (lq.1, ι lq.2)))⟩
        : AlterSeq State' Label)
        = (⟨s₀, Stream'.Seq.ofList L'⟩ : AlterSeq State Label).map ι := (hmapForm L').symm
    -- match the two factors
    congr 1
    · -- probOf factors: use IH
      rw [ProbabilisticExecution.probOf_congr peC _
        ((⟨s₀, Stream'.Seq.ofList L'⟩ : AlterSeq State Label).map ι) hmapL' _
        (hmapL' ▸ Stream'.Seq.terminates_ofList _)]
      exact ih (Stream'.Seq.terminates_ofList L') (hmapL' ▸ Stream'.Seq.terminates_ofList _)
    · -- kernel factors: use embedSched_kernel_transport with E = ⟨s₀, ofList L'⟩
      rw [hmapL']
      exact embedSched_kernel_transport hι hstep σ μ ⟨s₀, Stream'.Seq.ofList L'⟩ l s'

/-- **Support is contained in the `ι`-image.** Any `sys'`-execution `⟨i', ofList L⟩` with nonzero
probability under `⟨μ.map ι, embedSched⟩` is the `ι`-image of a `sys`-execution. Proven by cons-end
induction on the transition list `L`. -/
private theorem embedSched_probOf_image {sys : System State Label} {sys' : System State' Label}
    {ι : State → State'} (hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    (σ : WeakScheduler sys) (μ : PMF State) (i' : State') (L : List (Label × State'))
    (hne : (⟨μ.map ι, (embedSched hι hstep σ).toScheduler⟩
        : ProbabilisticExecution sys').probOf ⟨i', Stream'.Seq.ofList L⟩
          (Stream'.Seq.terminates_ofList _) ≠ 0) :
    ∃ E : AlterSeq State Label, E.map ι = ⟨i', Stream'.Seq.ofList L⟩ := by
  classical
  set peC : ProbabilisticExecution sys' := ⟨μ.map ι, (embedSched hι hstep σ).toScheduler⟩ with hpeC
  induction L using List.reverseRecOn with
  | nil =>
    rw [ProbabilisticExecution.probOf_congr peC _ ⟨i', Seq.nil⟩ (by rw [Stream'.Seq.ofList_nil])
      (Stream'.Seq.terminates_ofList _) Stream'.Seq.terminates_nil] at hne
    rw [ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState, hpeC] at hne
    have hi' : i' ∈ (μ.map ι).support := hne
    rw [PMF.mem_support_map_iff] at hi'
    obtain ⟨s₀, _, hs₀⟩ := hi'
    exact ⟨⟨s₀, Seq.nil⟩, by
      unfold AlterSeq.map; simp only [Stream'.Seq.map_nil, hs₀, Stream'.Seq.ofList_nil]⟩
  | append_singleton rest last ih =>
    obtain ⟨l, s'⟩ := last
    -- factor probOf over the last transition
    have hsplit_eq : (⟨i', Stream'.Seq.ofList (rest ++ [(l, s')])⟩ : AlterSeq State' Label)
        = ⟨i', (Stream'.Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ := by
      rw [ofList_append_singleton]
    rw [ProbabilisticExecution.probOf_congr peC _
      ⟨i', (Stream'.Seq.ofList rest).append (Seq.cons (l, s') Seq.nil)⟩ hsplit_eq
      (Stream'.Seq.terminates_ofList _) (hsplit_eq ▸ Stream'.Seq.terminates_ofList _)] at hne
    rw [ProbabilisticExecution.probOf_append_singleton peC i' (Stream'.Seq.ofList rest)
      (Stream'.Seq.terminates_ofList _) (l, s') _] at hne
    have hprob_ne :
        peC.probOf ⟨i', Stream'.Seq.ofList rest⟩ (Stream'.Seq.terminates_ofList _) ≠ 0 :=
      fun h => hne (by rw [h, zero_mul])
    have hker_ne : peC.kernel ⟨i', Stream'.Seq.ofList rest⟩ (l, s') ≠ 0 :=
      fun h => hne (by rw [h, mul_zero])
    obtain ⟨E₀, hE₀⟩ := ih hprob_ne
    -- kernel nonzero + on-image ⇒ s' = ι s
    rw [← hE₀] at hker_ne
    have hker_form : peC.kernel (E₀.map ι) (l, s')
        = ∑' m', (embedSched hι hstep σ).next (E₀.map ι) (some (l, m')) * m' s' := rfl
    rw [hker_form, embedSched_next_image hι hstep σ E₀] at hker_ne
    obtain ⟨m', hm'⟩ : ∃ m', ((σ.next E₀).map (embedEmit ι)) (some (l, m')) * m' s' ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hker_ne (by rw [ENNReal.tsum_eq_zero.mpr hall])
    have hnext_ne : ((σ.next E₀).map (embedEmit ι)) (some (l, m')) ≠ 0 :=
      fun h => hm' (by rw [h, zero_mul])
    have hm's' : m' s' ≠ 0 := fun h => hm' (by rw [h, mul_zero])
    rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at hnext_ne
    obtain ⟨o, _, hoeq⟩ := hnext_ne
    obtain ⟨m, _, hμ'⟩ := embedEmit_some hoeq
    subst hμ'
    rw [← PMF.mem_support_iff, PMF.mem_support_map_iff] at hm's'
    obtain ⟨s, _, hs⟩ := hm's'
    -- reconstruct the extended preimage execution
    refine ⟨⟨E₀.init, E₀.trans.append (Seq.cons (l, s) Seq.nil)⟩, ?_⟩
    rw [AlterSeq.map_append_singleton ι E₀ l s, hs, hE₀, hsplit_eq]

end EmbedNonempty

/-- **Embedding a τ-closure (the crux).** The witnessing `WeakScheduler` for `weakTau sys μ ν` is
mapped along `ι`: on an execution that is the `ι`-image of a `sys`-execution it re-emits the
`ι`-pushforward of the original emission; off the image it halts (`⊥`). Injectivity makes the
`ι`-image a clean copy, so the halting mass and end-state pushforward transport, giving
`weakTau sys' (μ.map ι) (ν.map ι)`. -/
theorem weakTau_embed {sys : System State Label} {sys' : System State' Label}
    (ι : State → State') (hι : Function.Injective ι)
    (hstep : ∀ s μ, sys.step s Silent.τ μ → sys'.step (ι s) Silent.τ (μ.map ι))
    {μ ν : PMF State} (h : weakTau sys μ ν) :
    weakTau sys' (μ.map ι) (ν.map ι) := by
  classical
  -- `State` is nonempty (from `μ`), so `Function.invFun ι` is available.
  have hne_state : Nonempty State := by
    by_contra hempty
    rw [not_nonempty_iff] at hempty
    exact absurd μ.tsum_coe (by rw [tsum_empty]; exact zero_ne_one)
  set σ := h.witnessScheduler with hσ
  set σ' := embedSched hι hstep σ with hσ'
  -- the injection from terminating `sys`-executions to their `ι`-images
  set g : {E : AlterSeq State Label // E.trans.Terminates}
      → {e' : AlterSeq State' Label // e'.trans.Terminates} :=
    fun E => ⟨E.1.map ι, (AlterSeq.map_trans_terminates_iff ι E.1).mpr E.2⟩ with hg
  have hg_inj : Function.Injective g := by
    rintro ⟨E₁, h₁⟩ ⟨E₂, h₂⟩ heq
    simp only [hg, Subtype.mk.injEq] at heq
    exact Subtype.ext (AlterSeq.map_injective hι heq)
  -- halt-mass transports along `g`
  have hHalt_g : ∀ E : {E : AlterSeq State Label // E.trans.Terminates},
      σ'.haltMass (μ.map ι) (g E) = σ.haltMass μ E := by
    rintro ⟨E, hE⟩
    unfold WeakScheduler.haltMass Scheduler.haltMass
    simp only [hg]
    -- probOf factor: bridge to `ofList` form then apply `embedSched_probOf`
    have hEform : E = ⟨E.init, Stream'.Seq.ofList (E.trans.toList hE)⟩ := by
      cases E; simp only [AlterSeq.mk.injEq, true_and]; rw [Stream'.Seq.ofList_toList]
    have hprob :
        (⟨μ.map ι, σ'.toScheduler⟩ : ProbabilisticExecution sys').probOf (E.map ι)
            ((AlterSeq.map_trans_terminates_iff ι E).mpr hE)
          = (⟨μ, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf E hE := by
      have hmapEq : E.map ι
          = (⟨E.init, Stream'.Seq.ofList (E.trans.toList hE)⟩ : AlterSeq State Label).map ι := by
        rw [← hEform]
      rw [ProbabilisticExecution.probOf_congr (⟨μ.map ι, σ'.toScheduler⟩) _
        ((⟨E.init, Stream'.Seq.ofList (E.trans.toList hE)⟩ : AlterSeq State Label).map ι) hmapEq _
        (hmapEq ▸ (AlterSeq.map_trans_terminates_iff ι E).mpr hE)]
      rw [ProbabilisticExecution.probOf_congr (⟨μ, σ.toScheduler⟩) E
        ⟨E.init, Stream'.Seq.ofList (E.trans.toList hE)⟩ hEform hE
        (hEform ▸ hE)]
      exact embedSched_probOf hι hstep σ μ E.init (E.trans.toList hE) _ _
    rw [hprob]
    -- none-mass factor: `σ'.next (E.map ι) none = σ.next E none`
    congr 1
    rw [hσ', embedSched_next_image hι hstep σ E, embedEmit_map_none]
  -- support of the mapped halt-mass lies in the range of `g`
  have hsupp : Function.support (σ'.haltMass (μ.map ι)) ⊆ Set.range g := by
    rintro ⟨e', hT'⟩ hmem
    rw [Function.mem_support] at hmem
    have hprob_ne :
        (⟨μ.map ι, σ'.toScheduler⟩ : ProbabilisticExecution sys').probOf e' hT' ≠ 0 := by
      intro h0; apply hmem
      unfold WeakScheduler.haltMass Scheduler.haltMass; rw [h0, zero_mul]
    -- bridge `e'` to `ofList` form and apply the image lemma
    have he'form : e' = ⟨e'.init, Stream'.Seq.ofList (e'.trans.toList hT')⟩ := by
      cases e'; simp only [AlterSeq.mk.injEq, true_and]; rw [Stream'.Seq.ofList_toList]
    have hprob_ofList :
        (⟨μ.map ι, σ'.toScheduler⟩ : ProbabilisticExecution sys').probOf
          ⟨e'.init, Stream'.Seq.ofList (e'.trans.toList hT')⟩ (Stream'.Seq.terminates_ofList _)
          ≠ 0 := by
      rw [ProbabilisticExecution.probOf_congr (⟨μ.map ι, σ'.toScheduler⟩)
        ⟨e'.init, Stream'.Seq.ofList (e'.trans.toList hT')⟩ e' he'form.symm
        (Stream'.Seq.terminates_ofList _) hT']
      exact hprob_ne
    obtain ⟨E, hE⟩ :=
      embedSched_probOf_image hι hstep σ μ e'.init (e'.trans.toList hT') hprob_ofList
    have hmapE : E.map ι = e' := by rw [hE, ← he'form]
    refine ⟨⟨E, (AlterSeq.map_trans_terminates_iff ι E).mp (hmapE ▸ hT')⟩, ?_⟩
    simp only [hg]
    exact Subtype.ext hmapE
  refine ⟨σ', ?_, ?_⟩
  · -- total halting mass = 1
    rw [← Function.Injective.tsum_eq hg_inj hsupp]
    rw [tsum_congr hHalt_g]
    exact h.witness_halts
  · -- end-state pushforward
    intro s'
    -- (ν.map ι) s' = ∑' s, ν s * [ι s = s']
    rw [PMF.map_apply]
    -- reindex the halt-mass sum along `g`
    rw [show (∑' e', σ'.haltMass (μ.map ι) e' * (if e'.1.endState e'.2 = s' then 1 else 0))
        = ∑' E, σ'.haltMass (μ.map ι) (g E)
            * (if (g E).1.endState (g E).2 = s' then 1 else 0) from by
      rw [← Function.Injective.tsum_eq hg_inj (f := fun e' =>
        σ'.haltMass (μ.map ι) e' * (if e'.1.endState e'.2 = s' then 1 else 0)) ?_]
      intro e' he'
      have : σ'.haltMass (μ.map ι) e' ≠ 0 := by
        intro h0; apply Function.mem_support.mp he'; rw [h0, zero_mul]
      obtain ⟨E, hE⟩ := hsupp (Function.mem_support.mpr this)
      exact ⟨E, hE⟩]
    -- endState (E.map ι) = ι (endState E); haltMass (g E) = haltMass σ μ E
    rw [show (∑' E, σ'.haltMass (μ.map ι) (g E) * (if (g E).1.endState (g E).2 = s' then 1 else 0))
        = ∑' E : {E : AlterSeq State Label // E.trans.Terminates},
            σ.haltMass μ E * (if ι (E.1.endState E.2) = s' then 1 else 0) from by
      refine tsum_congr (fun E => ?_)
      rw [hHalt_g E]
      congr 1
      -- (g E).1.endState (g E).2 = ι (E.1.endState E.2)
      simp only [hg]
      rw [AlterSeq.map_endState ι E.1 E.2]]
    -- integrate against the indicator: this is `h.witness_pushforward` composed with `ι`
    rw [show (∑' E : {E : AlterSeq State Label // E.trans.Terminates},
          σ.haltMass μ E * (if ι (E.1.endState E.2) = s' then 1 else 0))
        = ∑' s, ν s * (if ι s = s' then 1 else 0) from by
      rw [← weakTau.integrate h (fun s => if ι s = s' then 1 else 0)]]
    refine tsum_congr (fun s => ?_)
    rw [eq_comm (a := s'), mul_ite, mul_one, mul_zero]

/-- **Embedding a weak `l`-step.** The three layers `τ-closure ∘ hyperStep_l ∘ τ-closure` transport
by `weakTau_embed` (twice) and `hyperStep_embed` (once). Needs `ι` to preserve steps at *every*
label (satisfied by fully-asynchronous `interleave`; the synchronised `parallel` case is handled
separately). -/
theorem weakStep_embed {sys : System State Label} {sys' : System State' Label}
    (ι : State → State') (hι : Function.Injective ι) {l : Label}
    (hstep : ∀ s l' μ, sys.step s l' μ → sys'.step (ι s) l' (μ.map ι))
    {μ ν : PMF State} (h : weakStep sys μ l ν) :
    weakStep sys' (μ.map ι) l (ν.map ι) := by
  obtain ⟨m, m', h1, h2, h3⟩ := h
  exact ⟨m.map ι, m'.map ι,
    weakTau_embed ι hι (fun s μ => hstep s Silent.τ μ) h1,
    hyperStep_embed ι hι (fun s μ => hstep s l μ) h2,
    weakTau_embed ι hι (fun s μ => hstep s Silent.τ μ) h3⟩

end PLTS
