/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.Framework.TraceSupport
import Leslie2.ProcessAlgebra.Abstract
import Leslie2.Simulation.SimDefs
import Leslie2.Systems.LTS

/-!
# Extended alphabets and restriction along the left summand

A composition often needs labels that only exist to make its components
rendezvous — round tags, per-process handshakes, internal acknowledgements —
which the composite is not meant to expose. The idiom is to build the components
over the **extended alphabet** `Label ⊕ Extra`, where `Label` is the alphabet the
composite shares with everything else and `Extra` carries the auxiliary labels;
`System.abstract` (in `ProcessAlgebra/Composition.lean`) then hides the `Sum.inr`
labels as `τ`, and `System.relabel` transports the result back to `Label`:

* `System.relabel sys : System State Label` keeps the state space of
  `sys : System State (Label ⊕ Extra)` and retains exactly its `Sum.inl`-labelled
  transitions.

For that pipeline to typecheck, the extended alphabet needs its own silent label.
The instance `PLTS.instSilentSum` takes it to be `Sum.inl τ`, so that `τ` on
`Label ⊕ Extra` and `τ` on `Label` name the same transitions across `relabel`,
and every auxiliary label `Sum.inr e` is observable (hence hideable by
`abstract`).

Restriction discards transitions rather than states, so it preserves
`System.IsLTS` (`System.relabel_isLTS`).

## The precongruence

A probabilistic forward simulation survives the restriction
(`ProbabilisticForwardSimulation.relabel`).

The restriction changes the *label type*, and a weak transition
(`weakTau` / `weakStep`) is witnessed by a `WeakScheduler`, whose `next`
function is typed by that label type. The witness therefore has to be
transported rather than reused, which is what `WeakScheduler.relabel` does:
the emissions of `σ` are read along `relDown` (an auxiliary label would go to
`τ`, but a weak scheduler emits none), and the prefix it is asked about is
read back along `Sum.inl`.

Everything else follows the emission identities `relabel_next_none` and
`relabel_next_some`, which say that the transported scheduler puts exactly the
mass `σ` puts on the corresponding extended emission: the auxiliary preimages
of a base label all carry mass `0`, since a weak scheduler emits `τ` alone.
-/

namespace PLTS

variable {State Label Extra : Type}

/-- The silent label of an extended alphabet `Label ⊕ Extra` is the silent label
of the base alphabet, injected on the left. Every auxiliary label `Sum.inr e` is
therefore observable. -/
instance instSilentSum [Silent Label] : Silent (Label ⊕ Extra) := ⟨Sum.inl Silent.τ⟩

namespace System

/-- **Restriction along the left embedding.** `sys.relabel` reads a system over
the extended alphabet `Label ⊕ Extra` as a system over `Label`: the state space
and the initial state are unchanged, and the transitions on `l` are exactly the
`Sum.inl l`-transitions of `sys`. Transitions labelled by an auxiliary
`Sum.inr e` are discarded — abstract them to `τ` first if they are to survive. -/
def relabel (sys : System State (Label ⊕ Extra)) : System State Label where
  init := sys.init
  step s l μ := sys.step s (Sum.inl l) μ

@[simp] theorem relabel_init (sys : System State (Label ⊕ Extra)) :
    (sys.relabel).init = sys.init := rfl

@[simp] theorem relabel_step (sys : System State (Label ⊕ Extra))
    (s : State) (l : Label) (μ : PMF State) :
    (sys.relabel).step s l μ ↔ sys.step s (Sum.inl l) μ := Iff.rfl

/-- Restriction preserves the LTS property: its transitions are a sub-collection
of those of `sys`, so they still all lead to Diracs. -/
theorem relabel_isLTS {sys : System State (Label ⊕ Extra)} (h : sys.IsLTS) :
    (sys.relabel).IsLTS :=
  fun s l μ hstep => h s (Sum.inl l) μ hstep

end System

/-- Abstraction preserves the LTS property: it relabels transitions and keeps
each one's distribution. -/
theorem System.abstract_isLTS {State Label : Type} [Silent Label]
    {sys : System State Label} (h : sys.IsLTS) (L : Set Label) :
    (sys.abstract L).IsLTS := by
  rintro s l μ (⟨-, l', -, hstep⟩ | ⟨-, hstep⟩) <;> exact h s _ μ hstep

/-! ### The label projection -/

section RelabelWeak

variable {State Label Extra : Type} [Silent Label]

/-- Reading an extended label as a base label: `Sum.inl l` is `l`, and an
auxiliary label — which a weak scheduler never emits — is read as `τ`. -/
def relDown : Label ⊕ Extra → Label :=
  Sum.elim id (fun _ => Silent.τ)

@[simp] theorem relDown_inl (l : Label) :
    (relDown (Sum.inl l : Label ⊕ Extra)) = l := rfl

@[simp] theorem relDown_inr (e : Extra) :
    (relDown (Sum.inr e : Label ⊕ Extra)) = (Silent.τ : Label) := rfl

/-- The extended alphabet's silent label is the base one on the left. -/
theorem sum_tau_eq : (Silent.τ : Label ⊕ Extra) = Sum.inl (Silent.τ : Label) := rfl

/-- `Sum.inl` reflects the silent label. -/
theorem inl_eq_tau_iff (l : Label) :
    (Sum.inl l : Label ⊕ Extra) = (Silent.τ : Label ⊕ Extra) ↔ l = (Silent.τ : Label) :=
  ⟨fun h => Sum.inl_injective h, fun h => by rw [h]; rfl⟩

omit [Silent Label] in
/-- Termination of a run is untouched by relabelling its transitions. -/
theorem AlterSeq.mapLab_terminatedAt_iff {L L' : Type} (g : L → L')
    (e : AlterSeq State L) (n : ℕ) :
    (e.mapLab g).trans.TerminatedAt n ↔ e.trans.TerminatedAt n := by
  change (e.trans.map fun lq => (g lq.1, lq.2)).get? n = none ↔ e.trans.get? n = none
  rw [Stream'.Seq.map_get?]
  cases e.trans.get? n <;> simp

omit [Silent Label] in
/-- A run over a list of transitions, read on the extended alphabet. -/
theorem mapLab_ofList (s₀ : State) (L : List (Label × State)) :
    (⟨s₀, Stream'.Seq.ofList L⟩ : AlterSeq State Label).mapLab
        (Sum.inl : Label → Label ⊕ Extra)
      = ⟨s₀, Stream'.Seq.ofList (L.map (fun p => (Sum.inl p.1, p.2)))⟩ := by
  change (⟨s₀, (Stream'.Seq.ofList L).map _⟩ : AlterSeq State (Label ⊕ Extra)) = _
  rw [Stream'.Seq.map_ofList_pub]

/-! ### Transporting a weak scheduler -/

variable {sys : System State (Label ⊕ Extra)}

open Classical in
/-- **The transported weak scheduler.** `σ` is asked about the prefix read on
the extended alphabet, and its answer is read back along `relDown`. -/
noncomputable def WeakScheduler.relabel (σ : WeakScheduler sys) :
    WeakScheduler sys.relabel where
  next e := (σ.next (e.mapLab Sum.inl)).map (Option.map (fun p => (relDown p.1, p.2)))
  valid := by
    intro e n s hterm hstate l μ hsupp
    rw [PMF.mem_support_map_iff] at hsupp
    obtain ⟨o, hoS, hoE⟩ := hsupp
    cases o with
    | none => exact absurd hoE (by simp)
    | some p =>
      obtain ⟨m, ν⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoE
      obtain ⟨hm, rfl⟩ := hoE
      have hmτ : m = (Silent.τ : Label ⊕ Extra) := σ.internal_only _ m ν hoS
      have hstep := σ.valid (e.mapLab Sum.inl) n s
        ((AlterSeq.mapLab_terminatedAt_iff _ e n).mpr hterm)
        (by rw [AlterSeq.stateAt_mapLab]; exact hstate) m ν hoS
      subst hmτ
      have hl : l = (Silent.τ : Label) := by rw [← hm]; rfl
      subst hl
      exact hstep
  internal_only := by
    intro e l μ hsupp
    rw [PMF.mem_support_map_iff] at hsupp
    obtain ⟨o, hoS, hoE⟩ := hsupp
    cases o with
    | none => exact absurd hoE (by simp)
    | some p =>
      obtain ⟨m, ν⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hoE
      obtain ⟨hm, rfl⟩ := hoE
      have hmτ : m = (Silent.τ : Label ⊕ Extra) := σ.internal_only _ m ν hoS
      rw [← hm, hmτ]
      rfl

/-- The transported scheduler halts with exactly the mass `σ` halts with. -/
theorem WeakScheduler.relabel_next_none (σ : WeakScheduler sys)
    (e : AlterSeq State Label) :
    σ.relabel.next e none = σ.next (e.mapLab Sum.inl) none := by
  classical
  change ((σ.next (e.mapLab Sum.inl)).map (Option.map (fun p => (relDown p.1, p.2))))
    none = _
  rw [PMF.map_apply]
  refine (tsum_eq_single none ?_).trans (if_pos rfl)
  intro o ho
  refine if_neg ?_
  cases o with
  | none => exact absurd rfl ho
  | some p => simp

/-- The transported scheduler emits `(l, μ)` with exactly the mass `σ` emits
`(Sum.inl l, μ)` with: every auxiliary preimage of `l` carries mass `0`,
because a weak scheduler emits `τ` alone. -/
theorem WeakScheduler.relabel_next_some (σ : WeakScheduler sys)
    (e : AlterSeq State Label) (l : Label) (μ : PMF State) :
    σ.relabel.next e (some (l, μ)) = σ.next (e.mapLab Sum.inl) (some (Sum.inl l, μ)) := by
  classical
  change ((σ.next (e.mapLab Sum.inl)).map (Option.map (fun p => (relDown p.1, p.2))))
    (some (l, μ)) = _
  rw [PMF.map_apply]
  refine (tsum_eq_single (some (Sum.inl l, μ)) ?_).trans (if_pos rfl)
  intro o ho
  by_cases hmatch : (some (l, μ) : Option (Label × PMF State))
      = (Option.map (fun p : (Label ⊕ Extra) × PMF State => (relDown p.1, p.2))) o
  · rw [if_pos hmatch]
    cases o with
    | none => exact absurd hmatch (by simp)
    | some p =>
      obtain ⟨m, ν⟩ := p
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hmatch
      obtain ⟨hm, rfl⟩ := hmatch
      by_contra hne
      have hmτ : m = (Silent.τ : Label ⊕ Extra) :=
        σ.internal_only _ m μ (by rw [PMF.mem_support_iff]; exact hne)
      rw [hmτ] at hm
      exact ho (by rw [hmτ, hm]; rfl)
  · exact if_neg hmatch

/-! ### Path probabilities under the transported scheduler -/

omit [Silent Label] in
/-- `mapLab` composes. -/
theorem AlterSeq.mapLab_mapLab {L₁ L₂ L₃ : Type} (f : L₁ → L₂) (g : L₂ → L₃)
    (e : AlterSeq State L₁) : (e.mapLab f).mapLab g = e.mapLab (g ∘ f) := by
  change (⟨e.init, (e.trans.map _).map _⟩ : AlterSeq State L₃) = ⟨e.init, e.trans.map _⟩
  rw [← Stream'.Seq.map_comp]
  rfl

omit [Silent Label] in
/-- `mapLab` at a map fixing every label of the run is the identity. -/
theorem AlterSeq.mapLab_eq_self {L : Type} (g : L → L) (e : AlterSeq State L)
    (h : e.trans.Terminates)
    (hfix : ∀ p ∈ e.trans.toList h, g p.1 = p.1) : e.mapLab g = e := by
  have hlist : (e.trans.toList h).map (fun p : L × State => (g p.1, p.2))
      = e.trans.toList h :=
    (List.map_congr_left (fun p hp => by rw [hfix p hp]; rfl)).trans (List.map_id _)
  change (⟨e.init, e.trans.map _⟩ : AlterSeq State L) = e
  conv_lhs => rw [← Stream'.Seq.ofList_toList e.trans h, Stream'.Seq.map_ofList_pub, hlist]
  rw [Stream'.Seq.ofList_toList]

/-- The transition-list embedding along `Sum.inl`. -/
def relUp (p : Label × State) : (Label ⊕ Extra) × State := (Sum.inl p.1, p.2)

/-- Reading a run back along `relDown` undoes the embedding. -/
theorem AlterSeq.mapLab_relDown_mapLab_inl (e : AlterSeq State Label) :
    (e.mapLab (Sum.inl : Label → Label ⊕ Extra)).mapLab relDown = e := by
  rw [AlterSeq.mapLab_mapLab]
  change e.mapLab id = e
  change (⟨e.init, e.trans.map _⟩ : AlterSeq State Label) = e
  rw [show (fun lq : Label × State => (id lq.1, lq.2)) = id from rfl, Stream'.Seq.map_id]

section ProbTransport

variable {S L : Type} [Silent L] {sy : System S L}

omit [Silent L] in
/-- The cons-end factorisation of `probOf` on a run given by a list. -/
theorem probOf_ofList_concat (pe : ProbabilisticExecution sy) (s₀ : S)
    (rest : List (L × S)) (last : L × S) :
    pe.probOf ⟨s₀, Stream'.Seq.ofList (rest ++ [last])⟩ (Stream'.Seq.terminates_ofList _)
      = pe.probOf ⟨s₀, Stream'.Seq.ofList rest⟩ (Stream'.Seq.terminates_ofList _)
        * pe.kernel ⟨s₀, Stream'.Seq.ofList rest⟩ last := by
  unfold ProbabilisticExecution.probOf
  rw [Stream'.Seq.toList_ofList, List.reverseRecOn_concat, Stream'.Seq.toList_ofList]

end ProbTransport

variable {sys : System State (Label ⊕ Extra)}

/-- The one-step kernel is the one `σ` has at the embedded prefix. -/
theorem kernel_relabel (σ : WeakScheduler sys) (μ0 : PMF State)
    (e : AlterSeq State Label) (p : Label × State) :
    (⟨μ0, σ.relabel.toScheduler⟩ : ProbabilisticExecution sys.relabel).kernel e p
      = (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).kernel
          (e.mapLab Sum.inl) (relUp p) :=
  tsum_congr fun ν => by rw [σ.relabel_next_some]; rfl

/-- **Path probabilities are preserved**: the transported scheduler gives a
run over `Label` exactly the probability `σ` gives its embedding. -/
theorem probOf_relabel (σ : WeakScheduler sys) (μ0 : PMF State) (s₀ : State)
    (L : List (Label × State)) :
    (⟨μ0, σ.relabel.toScheduler⟩ : ProbabilisticExecution sys.relabel).probOf
        ⟨s₀, Stream'.Seq.ofList L⟩ (Stream'.Seq.terminates_ofList _)
      = (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Stream'.Seq.ofList (L.map relUp)⟩ (Stream'.Seq.terminates_ofList _) := by
  induction L using List.reverseRecOn with
  | nil =>
    rw [List.map_nil]
    unfold ProbabilisticExecution.probOf
    rw [Stream'.Seq.toList_ofList, Stream'.Seq.toList_ofList,
      List.reverseRecOn_nil, List.reverseRecOn_nil]
    rfl
  | append_singleton rest last ih =>
    rw [List.map_append, List.map_cons, List.map_nil, probOf_ofList_concat,
      probOf_ofList_concat, ih, kernel_relabel, mapLab_ofList]
    rfl

/-- A run of positive probability under a weak scheduler carries silent labels
only. -/
theorem tau_of_probOf_ne_zero (σ : WeakScheduler sys) (μ0 : PMF State) (s₀ : State)
    (L : List ((Label ⊕ Extra) × State))
    (hne : (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
      ⟨s₀, Stream'.Seq.ofList L⟩ (Stream'.Seq.terminates_ofList _) ≠ 0) :
    ∀ p ∈ L, p.1 = (Silent.τ : Label ⊕ Extra) := by
  induction L using List.reverseRecOn with
  | nil => intro p hp; exact absurd hp (by simp)
  | append_singleton rest last ih =>
    rw [probOf_ofList_concat] at hne
    have h1 : (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf
        ⟨s₀, Stream'.Seq.ofList rest⟩ (Stream'.Seq.terminates_ofList _) ≠ 0 :=
      fun h => hne (by rw [h, zero_mul])
    have h2 : (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).kernel
        ⟨s₀, Stream'.Seq.ofList rest⟩ last ≠ 0 :=
      fun h => hne (by rw [h, mul_zero])
    intro p hp
    rcases List.mem_append.mp hp with hp | hp
    · exact ih h1 p hp
    · have hpl : p = last := by simpa using hp
      subst hpl
      by_contra hτ
      refine h2 (ENNReal.tsum_eq_zero.mpr fun ν => ?_)
      by_cases hν : σ.next ⟨s₀, Stream'.Seq.ofList rest⟩ (some (p.1, ν)) = 0
      · rw [hν, zero_mul]
      · exact absurd (σ.internal_only _ p.1 ν (by rw [PMF.mem_support_iff]; exact hν)) hτ

/-! ### The halting mass -/

/-- The embedding of a terminating run into the extended alphabet. -/
noncomputable def relLift
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    {E : AlterSeq State (Label ⊕ Extra) // E.trans.Terminates} :=
  ⟨e.1.mapLab Sum.inl, (AlterSeq.mapLab_trans_terminates_iff _ e.1).mpr e.2⟩

theorem relLift_injective :
    Function.Injective (relLift (State := State) (Label := Label) (Extra := Extra)) := by
  intro e₁ e₂ h
  refine Subtype.ext ?_
  have h' : e₁.1.mapLab (Sum.inl : Label → Label ⊕ Extra)
      = e₂.1.mapLab Sum.inl := congrArg Subtype.val h
  calc (e₁ : AlterSeq State Label)
      = (e₁.1.mapLab (Sum.inl : Label → Label ⊕ Extra)).mapLab relDown :=
        (AlterSeq.mapLab_relDown_mapLab_inl e₁.1).symm
    _ = (e₂.1.mapLab (Sum.inl : Label → Label ⊕ Extra)).mapLab relDown := by rw [h']
    _ = (e₂ : AlterSeq State Label) := AlterSeq.mapLab_relDown_mapLab_inl e₂.1

/-- **The halting mass is preserved**. -/
theorem haltMass_relabel (σ : WeakScheduler sys) (μ0 : PMF State)
    (e : {e : AlterSeq State Label // e.trans.Terminates}) :
    σ.relabel.haltMass μ0 e = σ.haltMass μ0 (relLift e) := by
  obtain ⟨e, h⟩ := e
  have he : e = (⟨e.init, Stream'.Seq.ofList (e.trans.toList h)⟩ : AlterSeq State Label) := by
    rw [Stream'.Seq.ofList_toList]
  have he2 : e.mapLab (Sum.inl : Label → Label ⊕ Extra)
      = ⟨e.init, Stream'.Seq.ofList ((e.trans.toList h).map relUp)⟩ := by
    conv_lhs => rw [he]
    exact mapLab_ofList _ _
  change (⟨μ0, σ.relabel.toScheduler⟩ : ProbabilisticExecution sys.relabel).probOf e h
      * σ.relabel.next e none
    = (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf (e.mapLab Sum.inl) _
      * σ.next (e.mapLab Sum.inl) none
  rw [σ.relabel_next_none,
    ProbabilisticExecution.probOf_congr _ e _ he h (Stream'.Seq.terminates_ofList _),
    ProbabilisticExecution.probOf_congr _ (e.mapLab Sum.inl) _ he2 _
      (Stream'.Seq.terminates_ofList _),
    probOf_relabel]

/-- A run the weak scheduler gives positive halting mass to is the embedding of
a run over the base alphabet: all its labels are `τ = Sum.inl τ`. -/
theorem exists_relLift_of_haltMass_ne_zero (σ : WeakScheduler sys) (μ0 : PMF State)
    (E : {E : AlterSeq State (Label ⊕ Extra) // E.trans.Terminates})
    (hne : σ.haltMass μ0 E ≠ 0) : ∃ e, relLift e = E := by
  obtain ⟨E, hE⟩ := E
  have hprob : (⟨μ0, σ.toScheduler⟩ : ProbabilisticExecution sys).probOf E hE ≠ 0 := by
    intro h
    exact hne (by change _ * _ = 0; rw [h, zero_mul])
  have hEeq : E = (⟨E.init, Stream'.Seq.ofList (E.trans.toList hE)⟩ :
      AlterSeq State (Label ⊕ Extra)) := by rw [Stream'.Seq.ofList_toList]
  have hτ : ∀ p ∈ E.trans.toList hE, p.1 = (Silent.τ : Label ⊕ Extra) := by
    refine tau_of_probOf_ne_zero σ μ0 E.init _ ?_
    rw [← ProbabilisticExecution.probOf_congr _ E _ hEeq hE (Stream'.Seq.terminates_ofList _)]
    exact hprob
  refine ⟨⟨E.mapLab relDown, (AlterSeq.mapLab_trans_terminates_iff _ E).mpr hE⟩,
    Subtype.ext ?_⟩
  change (E.mapLab relDown).mapLab (Sum.inl : Label → Label ⊕ Extra) = E
  rw [AlterSeq.mapLab_mapLab]
  exact AlterSeq.mapLab_eq_self _ E hE (fun p hp => by rw [hτ p hp]; rfl)

/-- **Reindexing the halting sums.** Any quantity that vanishes off the halting
support of `σ` sums over the extended runs exactly as it sums over their base
preimages. -/
theorem tsum_relLift (σ : WeakScheduler sys) (μ0 : PMF State)
    (F : {E : AlterSeq State (Label ⊕ Extra) // E.trans.Terminates} → ENNReal)
    (hF : ∀ E, σ.haltMass μ0 E = 0 → F E = 0) :
    (∑' E, F E) = ∑' e, F (relLift e) := by
  classical
  refine tsum_eq_tsum_of_ne_zero_bij
    (i := fun x : Function.support (fun e => F (relLift e)) => relLift (x : _)) ?_ ?_ ?_
  · intro x y hxy
    exact Subtype.ext (relLift_injective hxy)
  · intro E hE
    have hne : σ.haltMass μ0 E ≠ 0 := by
      intro h
      exact (Function.mem_support.mp hE) (hF E h)
    obtain ⟨e, he⟩ := exists_relLift_of_haltMass_ne_zero σ μ0 E hne
    refine ⟨⟨e, ?_⟩, he⟩
    rw [Function.mem_support, he]
    exact Function.mem_support.mp hE
  · intro x
    rfl

/-! ### The congruence -/

/-- **A τ-closure survives the restriction.** -/
theorem weakTau_relabel {μ0 ν : PMF State} (h : weakTau sys μ0 ν) :
    weakTau sys.relabel μ0 ν := by
  classical
  obtain ⟨σ, hsum, hpush⟩ := h
  refine ⟨σ.relabel, ?_, ?_⟩
  · rw [tsum_congr (fun e => haltMass_relabel σ μ0 e), ← tsum_relLift σ μ0 _ (fun _ h => h)]
    exact hsum
  · intro s
    rw [hpush s,
      tsum_relLift σ μ0 (fun E => σ.haltMass μ0 E * (if E.1.endState E.2 = s then 1 else 0))
        (fun E h => by rw [h, zero_mul])]
    refine tsum_congr fun e => ?_
    rw [haltMass_relabel σ μ0 e]
    congr 1
    refine if_congr (Iff.of_eq (congrArg (fun x => x = s) ?_)) rfl rfl
    change (e.1.mapLab (Sum.inl : Label → Label ⊕ Extra)).endState _ = e.1.endState e.2
    exact AlterSeq.endState_mapLab _ e.1 e.2 _

omit [Silent Label] in
/-- **A hyper-step survives the restriction**: the step relations coincide. -/
theorem hyperStep_relabel {μ ν : PMF State} {l : Label}
    (h : hyperStep sys μ (Sum.inl l) ν) : hyperStep sys.relabel μ l ν := by
  obtain ⟨p, hp, hν⟩ := h
  exact ⟨p, hp, hν⟩

/-- **A weak `l`-step survives the restriction**, segment by segment. -/
theorem weakStep_relabel {μ ν : PMF State} {l : Label}
    (h : weakStep sys μ (Sum.inl l) ν) : weakStep sys.relabel μ l ν := by
  obtain ⟨a, b, h1, h2, h3⟩ := h
  exact ⟨a, b, weakTau_relabel h1, hyperStep_relabel h2, weakTau_relabel h3⟩

/-- **Precongruence for restriction along the left summand.** A probabilistic
forward simulation over the extended alphabet `Label ⊕ Extra` restricts to one
over `Label`: the `Sum.inl`-transitions are the transitions of the restriction,
and the two silent labels name the same thing, so the weak answers transport
along `WeakScheduler.relabel`. -/
theorem ProbabilisticForwardSimulation.relabel {State_C State_A : Type}
    {sysC : System State_C (Label ⊕ Extra)} {sysA : System State_A (Label ⊕ Extra)}
    {R : State_C → PMF State_A → Prop}
    (sim : ProbabilisticForwardSimulation sysC sysA R) :
    ProbabilisticForwardSimulation sysC.relabel sysA.relabel R := by
  refine ⟨sim.init, ?_⟩
  intro s_C μ_A hR l μ_C hstep
  obtain ⟨ω, hPMFRel, hdisj⟩ := sim.step s_C μ_A hR (Sum.inl l) μ_C hstep
  refine ⟨ω, hPMFRel, ?_⟩
  rcases hdisj with ⟨hτ, hweak⟩ | ⟨hτ, hweak⟩
  · exact Or.inl ⟨(inl_eq_tau_iff l).mp hτ, weakTau_relabel hweak⟩
  · exact Or.inr ⟨fun h => hτ ((inl_eq_tau_iff l).mpr h), weakStep_relabel hweak⟩

end RelabelWeak

end PLTS
