/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sathiya / Claude
-/

import Leslie2Protocols.ABA.Protocol
import Leslie2Protocols.ABA.Hybrid

/-!
# The protocol under its composed reading

The protocol reading of `ABA/Protocol.lean` and the composed reading of
`ABA/Hybrid.lean` present one protocol at two cuts. A process record of the
protocol carries the round-loop record and the stage record of the round the
loop is in, and nothing else (D20). A composed state carries one
graded-agreement instance per round, at every moment. The round instances a
process has left keep their
stage records; no protocol state holds them. The composed reading therefore
holds strictly more state than the protocol one, and the two are related by a
relation, not by a map.

## The relation

`ProtocolRel` pins, of a composed state, everything a protocol state determines.

* The round loops are the first components of the process records.
* The coin oracle is the same component on both sides.
* The ABA-side network is the protocol adversary's DECIDED pools beside its
  corrupted set.
* The fabric of round `r` is the adversary's round-`r` message pools beside the
  same corrupted set. Corruption is one broadcast on both sides, so every copy
  of the corrupted set is the adversary's.
* The stage record of a process is the *live column*: the entry, at that
  process, of the instance of the round its round loop is in.
* Above a process's round the composed columns are pristine: a round the process
  has not reached holds the initial stage record at that process. This is what
  the round advance consumes. A protocol advance resets the stage record, and
  the composed side answers with the pristine column of the round just opened.
* Below a process's round the composed columns are unconstrained. Frozen history
  is specification-side state, and nothing in the protocol system reads it.

The last conjunct records that a process which has not been called is idle in
round `0`. It is what the external input row consumes: that row opens round `0`,
and the live column of the successor is the live column of the predecessor only
because the predecessor was already in round `0`.

## What this file supplies

`protocolSim`, a probabilistic forward simulation of `composed P` by
`protocol P` along the Dirac lift of `ProtocolRel P`, and the trace-distribution
inclusion `protocol_composed` it yields. The inclusion is one-directional: the
composed reading can retain a stage record no protocol state carries, so
the converse reading does not hold.
-/

namespace PLTS
namespace ABA

open Net Comp

/-- **The relation of the protocol presentation to the composed one.** Writing
`u = (procs, w, o)` and `t = (G, C, A, o')`, the seven conjuncts are: the round
loops agree; the oracle is shared; the ABA-side network is the adversary's
DECIDED pools; each round's fabric is that round's slice of the adversary's
pools beside the adversary's corrupted set; the live column of a process is its
stage record; the columns above a process's round are pristine at that process;
and a process with no input is idle in round `0`. Columns below a process's
round are unconstrained (D20). -/
def ProtocolRel (P : Params) (u : ProtocolState P) (t : ComposedState P) : Prop :=
  (∀ j, (u.1 j).1 = t.2.1 j) ∧
  u.2.2 = t.2.2.2 ∧
  t.2.2.1 = ⟨u.2.1.dpool, u.2.1.F⟩ ∧
  (∀ r, (t.1 r).2 = ⟨u.2.1.pool r, u.2.1.F⟩) ∧
  (∀ j, (t.1 (u.1 j).1.proc.round).1 j = (u.1 j).2) ∧
  (∀ j r, (u.1 j).1.proc.round < r → (t.1 r).1 j = GBCA.StageRec.initial P.n) ∧
  (∀ j, (u.1 j).1.proc.input = none →
    (u.1 j).1.proc.phase = Phase.idle ∧ (u.1 j).1.proc.round = 0)

/-- The relation, read at an explicit pair of states. -/
theorem protocolRel_mk (P : Params) (procs : ∀ _ : Fin P.n, ProcRec P.n) (w : NetState P.n)
    (o : ℕ → WCC.SpecState P.n) (G : ℕ → GBCA.ImplState P.n)
    (C : ∀ _ : Fin P.n, CoreRec P.n) (A : ANetState P.n)
    (o' : ℕ → WCC.SpecState P.n) :
    ProtocolRel P (procs, w, o) (G, C, A, o') ↔
      (∀ j, (procs j).1 = C j) ∧
      o = o' ∧
      A = ⟨w.dpool, w.F⟩ ∧
      (∀ r, (G r).2 = ⟨w.pool r, w.F⟩) ∧
      (∀ j, (G (procs j).1.proc.round).1 j = (procs j).2) ∧
      (∀ j r, (procs j).1.proc.round < r → (G r).1 j = GBCA.StageRec.initial P.n) ∧
      (∀ j, (procs j).1.proc.input = none →
        (procs j).1.proc.phase = Phase.idle ∧ (procs j).1.proc.round = 0) :=
  Iff.rfl

/-! ### Couplings

Every protocol transition is a product of Dirac factors beside the oracle's
successor distribution, and so is the composed transition that answers it. The
coupling is functional in the oracle coordinate: the two presentations carry the
same oracle, so a protocol outcome and the composed outcome that matches it
differ in no coordinate the relation constrains. -/

/-- A product of two Dirac factors beside a third distribution. -/
private theorem prodPMF_pure₂ {α β γ : Type*} (a : α) (b : β) (ν : PMF γ) :
    prodPMF (PMF.pure a) (prodPMF (PMF.pure b) ν) = ν.map (fun c => (a, b, c)) := by
  rw [prodPMF_pure_left, prodPMF_pure_left, PMF.map_comp]
  rfl

/-- A product of three Dirac factors beside a fourth distribution. -/
private theorem prodPMF_pure₃ {α β γ δ : Type*} (a : α) (b : β) (c : γ) (ν : PMF δ) :
    prodPMF (PMF.pure a) (prodPMF (PMF.pure b) (prodPMF (PMF.pure c) ν)) =
      ν.map (fun d => (a, b, c, d)) := by
  rw [prodPMF_pure_left, prodPMF_pure₂, PMF.map_comp]
  rfl

/-- A Dirac protocol outcome matched by a single related composed state. -/
private theorem match_pure (P : Params) {s : ProtocolState P} {t : ComposedState P}
    (h : ProtocolRel P s t) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (PMF.pure s) Ω ∧ Ω.bind id = PMF.pure t := by
  refine ⟨PMF.pure (PMF.pure t), ⟨PMF.pure (s, PMF.pure t), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp
    rw [PMF.mem_support_pure_iff] at hp
    subst hp
    exact ⟨t, rfl, h⟩
  · rw [PMF.pure_bind]
    rfl

/-- A protocol outcome whose only free coordinate is the oracle's, matched
outcome by outcome. -/
private theorem match_prod (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {G : ℕ → GBCA.ImplState P.n}
    {C : ∀ _ : Fin P.n, CoreRec P.n} {A : ANetState P.n}
    {ν : PMF (ℕ → WCC.SpecState P.n)}
    (h : ∀ o ∈ ν.support, ProtocolRel P (x, w, o) (G, C, A, o)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) (prodPMF (PMF.pure x) (prodPMF (PMF.pure w) ν)) Ω ∧
      Ω.bind id =
        prodPMF (PMF.pure G) (prodPMF (PMF.pure C) (prodPMF (PMF.pure A) ν)) := by
  refine ⟨ν.map (fun o => PMF.pure ((G, C, A, o) : ComposedState P)),
    ⟨ν.map (fun o => (((x, w, o) : ProtocolState P),
      PMF.pure ((G, C, A, o) : ComposedState P))), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.map_comp, prodPMF_pure₂]
    rfl
  · rw [PMF.map_comp]
    rfl
  · intro p hp
    rw [PMF.mem_support_map_iff] at hp
    obtain ⟨o, ho, rfl⟩ := hp
    exact ⟨(G, C, A, o), rfl, h o ho⟩
  · rw [PMF.bind_map, prodPMF_pure₃]
    rfl

/-! ### Updating one round

A label owned by round `r` moves that round's instance and no other. The two
lemmas below read the stage columns and the fabrics of the updated family. -/

/-- Updating round `r` by a state whose stage columns are the ones it already
had leaves every stage column where it was. -/
private theorem update_fst {P : Params} (G : ℕ → GBCA.ImplState P.n) (r : ℕ)
    {X : GBCA.ImplState P.n} (hX : X.1 = (G r).1) (r' : ℕ) :
    (Function.update G r X r').1 = (G r').1 := by
  by_cases h : r' = r
  · subst h; rw [Function.update_self, hX]
  · rw [Function.update_of_ne h]

/-- Updating round `r` by a state whose fabric is the one it already had leaves
every fabric where it was. -/
private theorem update_snd {P : Params} (G : ℕ → GBCA.ImplState P.n) (r : ℕ)
    (u : ∀ _ : Fin P.n, GBCA.StageRec P.n) (r' : ℕ) :
    (Function.update G r (u, (G r).2) r').2 = (G r').2 := by
  by_cases h : r' = r
  · subst h; rw [Function.update_self]
  · rw [Function.update_of_ne h]

/-- The fabric conjunct after a stage multicast in round `r`. -/
private theorem rel_gpool {P : Params} {G : ℕ → GBCA.ImplState P.n}
    {w : NetState P.n} (hG : ∀ r, (G r).2 = ⟨w.pool r, w.F⟩)
    (r : ℕ) (k : Fin P.n) (m : GBCA.Msg) (u : ∀ _ : Fin P.n, GBCA.StageRec P.n)
    (r' : ℕ) :
    ((Function.update G r (u, ((G r).2).gpool k m)) r').2 =
      ⟨(w.gpool r k m).pool r', (w.gpool r k m).F⟩ := by
  by_cases hr : r' = r
  · subst hr
    rw [Function.update_self]
    change ((G r').2).gpool k m = _
    rw [hG r']
    simp [GSub.GNetState.gpool]
  · rw [Function.update_of_ne hr, hG r', gpool_pool_ne w r k m hr]
    simp

/-- The fabric's corruption act and the adversary's agree. -/
private theorem corrupt_gnet {P : Params} (w : NetState P.n) (k : Fin P.n) (r : ℕ) :
    (⟨w.pool r, w.F⟩ : GSub.GNetState P.n).corrupt P k =
      ⟨(NetState.corrupt P k w).pool r, (NetState.corrupt P k w).F⟩ := by
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f <;>
    simp [GSub.GNetState.corrupt, NetState.corrupt, hc]

/-- The ABA-side network's corruption act and the adversary's agree. -/
private theorem corrupt_anet {P : Params} (w : NetState P.n) (k : Fin P.n) :
    ANetState.corrupt P k ⟨w.dpool, w.F⟩ =
      ⟨(NetState.corrupt P k w).dpool, (NetState.corrupt P k w).F⟩ := by
  by_cases hc : k ∉ w.F ∧ w.F.card < P.f <;>
    simp [ANetState.corrupt, NetState.corrupt, hc]

/-! ### Transporting the stage conjuncts

The three conjuncts that speak of the stage columns are read process by
process. Under a transition at which one process writes and the composed family
leaves every other column alone, they follow from the mover's own three facts
and from the conjuncts before the step. -/

/-- The stage conjuncts under a write at one process. -/
private theorem rel_one (P : Params) {procs x : ∀ _ : Fin P.n, ProcRec P.n}
    {G G' : ℕ → GBCA.ImplState P.n} (id : Fin P.n)
    (hlive : ∀ j, (G (procs j).1.proc.round).1 j = (procs j).2)
    (hfut : ∀ j r, (procs j).1.proc.round < r → (G r).1 j = GBCA.StageRec.initial P.n)
    (hidle : ∀ j, (procs j).1.proc.input = none →
      (procs j).1.proc.phase = Phase.idle ∧ (procs j).1.proc.round = 0)
    (hfor : ∀ i, i ≠ id → x i = procs i)
    (hGfor : ∀ j r, j ≠ id → (G' r).1 j = (G r).1 j)
    (hown : (G' (x id).1.proc.round).1 id = (x id).2)
    (hownf : ∀ r, (x id).1.proc.round < r → (G' r).1 id = GBCA.StageRec.initial P.n)
    (howni : (x id).1.proc.input = none →
      (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0) :
    (∀ j, (G' (x j).1.proc.round).1 j = (x j).2) ∧
    (∀ j r, (x j).1.proc.round < r → (G' r).1 j = GBCA.StageRec.initial P.n) ∧
    (∀ j, (x j).1.proc.input = none →
      (x j).1.proc.phase = Phase.idle ∧ (x j).1.proc.round = 0) := by
  refine ⟨fun j => ?_, fun j r hr => ?_, fun j hj => ?_⟩
  · by_cases h : j = id
    · subst h; exact hown
    · rw [hfor j h, hGfor j _ h]; exact hlive j
  · by_cases h : j = id
    · subst h; exact hownf r hr
    · rw [hfor j h] at hr; rw [hGfor j r h]; exact hfut j r hr
  · by_cases h : j = id
    · subst h; exact howni hj
    · rw [hfor j h] at hj ⊢; exact hidle j hj

/-- The stage conjuncts under a transition at which no process writes. -/
private theorem rel_none (P : Params) {procs x : ∀ _ : Fin P.n, ProcRec P.n}
    {G G' : ℕ → GBCA.ImplState P.n}
    (hlive : ∀ j, (G (procs j).1.proc.round).1 j = (procs j).2)
    (hfut : ∀ j r, (procs j).1.proc.round < r → (G r).1 j = GBCA.StageRec.initial P.n)
    (hidle : ∀ j, (procs j).1.proc.input = none →
      (procs j).1.proc.phase = Phase.idle ∧ (procs j).1.proc.round = 0)
    (hfor : ∀ i, x i = procs i)
    (hGfor : ∀ j r, (G' r).1 j = (G r).1 j) :
    (∀ j, (G' (x j).1.proc.round).1 j = (x j).2) ∧
    (∀ j r, (x j).1.proc.round < r → (G' r).1 j = GBCA.StageRec.initial P.n) ∧
    (∀ j, (x j).1.proc.input = none →
      (x j).1.proc.phase = Phase.idle ∧ (x j).1.proc.round = 0) := by
  refine ⟨fun j => ?_, fun j r hr => ?_, fun j hj => ?_⟩
  · rw [hfor j, hGfor j]; exact hlive j
  · rw [hfor j] at hr; rw [hGfor j r]; exact hfut j r hr
  · rw [hfor j] at hj ⊢; exact hidle j hj

/-! ### Assembling a composed transition

Two shapes of answer. A label the composed system takes on the nose is
answered by the rows of its four components. A stage rendezvous has no row at
three of them: it is internal to a round instance, and the family carries it
as its own silent rule. -/

/-- A visible label of the extended alphabet answered by the four composed
rows, the oracle's successor carried across. -/
private theorem match_vis (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w' : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {ω : PMF (ℕ → WCC.SpecState P.n)}
    {G G' : ℕ → GBCA.ImplState P.n} {C C' : ∀ _ : Fin P.n, CoreRec P.n}
    {A A' : ANetState P.n} {L : NLab P.n} (hL : L ≠ Silent.τ)
    (hrel : ∀ o' ∈ ω.support, ProtocolRel P (x, w', o') (G', C', A', o'))
    (hGs : (GSub.gbcaSide P).step G L (PMF.pure G'))
    (hCs : ∀ i, CoreProcStepN P i (C i) L (PMF.pure (C' i)))
    (hAs : ANetStep P A L (PMF.pure A'))
    (hWs : (wccLift P).step o L ω) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedPre P).step (G, C, A, o) L (Ω.bind id) := by
  obtain ⟨Ω, hr, hbind⟩ := match_prod P hrel
  exact ⟨Ω, hr, hbind ▸ composedPre_vis_step P hL hGs hCs hAs hWs⟩

/-- A rendezvous the composed reading answers inside one round: the
instance of round `r` takes it as its own silent rule. -/
private theorem match_round (P : Params) {x : ∀ _ : Fin P.n, ProcRec P.n}
    {w' : NetState P.n} {o : ℕ → WCC.SpecState P.n} {ν : PMF (ℕ → WCC.SpecState P.n)}
    {G : ℕ → GBCA.ImplState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} {r : ℕ} {X : GBCA.ImplState P.n} (hν : ν = PMF.pure o)
    (hrel : ProtocolRel P (x, w', o) (Function.update G r X, C, A, o))
    (hsub : (GSub.sub P r).step (G r) (Sum.inl Lab.tau) (PMF.pure X)) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
      (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
  subst hν
  obtain ⟨Ω, hr, hbind⟩ := match_pure P hrel
  refine ⟨Ω, ?_, ?_⟩
  · rw [prodPMF_pure_pure, prodPMF_pure_pure]; exact hr
  · rw [hbind]
    exact composedGroup_of_tau P (composedPre_tau_gbca P (gbcaSide_tau P G r hsub))

/-! ### The drive rows the protocol process group cannot take

A Byzantine graded-agreement call or return names a process, and the protocol
program of that process has no row for it (D11, D20). The process group is a
full synchronisation, so no protocol transition carries either label. -/

/-- The Byzantine graded-agreement call has no row at the process it names
(D11, D20). -/
private theorem stepN_byzCallG_dead {P : Params} {j : Fin P.n} {q : ProcRec P.n}
    {ν : PMF (ProcRec P.n)} {r : ℕ} {b : Bool}
    (h : ABAProcStepN P j q (Sum.inr (.byzCallG r j b)) ν) : False := by
  cases h with
  | byzCallGIdle _ _ _ _ _ hk => exact hk rfl

/-- The Byzantine graded-agreement return has no row at the process it names
(D11, D20). -/
private theorem stepN_byzRetG_dead {P : Params} {j : Fin P.n} {q : ProcRec P.n}
    {ν : PMF (ProcRec P.n)} {r : ℕ} {out : GbcaOut}
    (h : ABAProcStepN P j q (Sum.inr (.byzRetG r j out)) ν) : False := by
  cases h with
  | byzRetGIdle _ _ _ _ _ hk => exact hk rfl

/-! ### The matching, by label class

A transition of the protocol group is a hidden rendezvous, a visible shared
label, or the silent label. Each is answered by a transition of the composed
group on the same label, built from the rows of the four composed components. -/

/-- The matching on the rendezvous alphabet. -/
theorem match_event (P : Params) {procs : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ImplState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (procs, w, o) (G, C, A, o))
    (e : NetEvt P.n) {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (procs, w, o) (Sum.inr e) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
  obtain ⟨hC, -, hA, hG, hlive, hfut, hidle⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (procs i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ν, hall, hn, hWs, rfl⟩ := protocolPre_event_inv P h
  have hLne : (Sum.inr e : NLab P.n) ≠ Silent.τ := by simp
  have hvis : ∀ {G' : ℕ → GBCA.ImplState P.n} {A' : ANetState P.n},
      (∀ o' ∈ ν.support, ProtocolRel P (x, w', o') (G', fun i => (x i).1, A', o')) →
      (GSub.gbcaSide P).step G (Sum.inr e) (PMF.pure G') →
      (∀ i, CoreProcStepN P i (C i) (Sum.inr e) (PMF.pure ((x i).1))) →
      ANetStep P A (Sum.inr e) (PMF.pure A') →
      ∃ Ω : PMF (PMF (ComposedState P)),
        PMFRel (diracRel (ProtocolRel P))
          (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ν)) Ω ∧
        (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
    intro G' A' hrel hGs hCs hAs
    obtain ⟨Ω, hr, hs⟩ := match_vis P hLne hrel hGs hCs hAs hWs
    exact ⟨Ω, hr, composedGroup_of_event P e hs⟩
  cases e with
  | gsnd r j m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gsnd r j m) ν).mp hWs
    obtain rfl : w' = w.gpool r j m := pureN_inj (netStep_gsnd hn)
    have hcolr : ∀ _ : (procs j).1.proc.round = r, (G r).1 j = (procs j).2 :=
      fun hrr => by rw [← hrr]; exact hlive j
    have hstage : ∃ nd : GBCA.StageRec P.n,
        (procs j).1.proc.round = r ∧
        GSub.GProcStep P r j ((G r).1 j) (Sum.inr (GSub.GEvt.snd j m)) (PMF.pure nd) ∧
        x j = ((procs j).1, nd) := by
      cases m with
      | input b =>
        obtain ⟨hrr, hin, hcnt, hsend, hxid⟩ := stepN_gsnd_input_self (hall j)
        exact ⟨_, hrr, GSub.GProcStep.sndRelay _ b (by rw [hcolr hrr]; exact hin)
          (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hsend),
          by rw [hcolr hrr]; exact pureN_inj hxid⟩
      | echo b =>
        obtain ⟨hrr, hin, hcnt, hsend, hxid⟩ := stepN_gsnd_echo_self (hall j)
        exact ⟨_, hrr, GSub.GProcStep.sndEcho _ b (by rw [hcolr hrr]; exact hin)
          (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hsend),
          by rw [hcolr hrr]; exact pureN_inj hxid⟩
      | vote v =>
        cases v with
        | some b =>
          obtain ⟨hrr, hin, hcnt, hsend, hxid⟩ := stepN_gsnd_voteBit_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndVoteBit _ b (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
        | none =>
          obtain ⟨hrr, hin, hcnt, hval, hsend, hxid⟩ := stepN_gsnd_voteBot_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndVoteBot _ (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hval)
            (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
      | bind v =>
        cases v with
        | some b =>
          obtain ⟨hrr, hin, hcnt, hsend, hxid⟩ := stepN_gsnd_bindBit_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndBindBit _ b (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
        | none =>
          obtain ⟨hrr, hin, hcnt, hval, hsend, hxid⟩ := stepN_gsnd_bindBot_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndBindBot _ (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hval)
            (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
      | «seal» v =>
        cases v with
        | some b =>
          obtain ⟨hrr, hin, hcnt, hsend, hxid⟩ := stepN_gsnd_sealBit_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndSealBit _ b (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
        | none =>
          obtain ⟨hrr, hin, hcnt, hval, hsend, hxid⟩ := stepN_gsnd_sealBot_self (hall j)
          exact ⟨_, hrr, GSub.GProcStep.sndSealBot _ (by rw [hcolr hrr]; exact hin)
            (by rw [hcolr hrr]; exact hcnt) (by rw [hcolr hrr]; exact hval)
            (by rw [hcolr hrr]; exact hsend),
            by rw [hcolr hrr]; exact pureN_inj hxid⟩
    obtain ⟨nd, hrr, hrow, hx⟩ := hstage
    have hfor : ∀ i, i ≠ j → x i = procs i := fun i hi =>
      pureN_inj (stepN_gsnd_foreign (Ne.symm hi) (hall i))
    have hGfor : ∀ i r', i ≠ j →
        ((Function.update G r
          (Function.update ((G r).1) j nd, ((G r).2).gpool j m)) r').1 i =
            (G r').1 i := by
      intro i r' hi
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hi _ _
      · rw [Function.update_of_ne hr']
    have hown : ((Function.update G r
        (Function.update ((G r).1) j nd, ((G r).2).gpool j m))
          (x j).1.proc.round).1 j = (x j).2 := by
      simp only [hx, hrr, Function.update_self]
    have hownf : ∀ r', (x j).1.proc.round < r' →
        ((Function.update G r
          (Function.update ((G r).1) j nd, ((G r).2).gpool j m)) r').1 j =
            GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, hrr] at hr'
      rw [Function.update_of_ne (Nat.ne_of_gt hr')]
      exact hfut j r' (by rw [hrr]; exact hr')
    have howni : (x j).1.proc.input = none →
        (x j).1.proc.phase = Phase.idle ∧ (x j).1.proc.round = 0 := by
      simp only [hx]; exact hidle j
    have hxcore : ∀ i, (x i).1 = C i := by
      intro i
      by_cases hi : i = j
      · subst hi; rw [hx]; exact hC i
      · rw [hfor i hi]; exact hC i
    obtain ⟨h5, h6, h7⟩ := rel_one P j hlive hfut hidle hfor hGfor hown hownf howni
    exact match_round P rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨hxcore, rfl, by simpa using hA, rel_gpool hG r j m _, h5, h6, h7⟩)
      (GSub.sub_event_step P r (GSub.GEvt.snd j m)
        (gprocs_family j nd hrow
          (fun i hi => GSub.GProcStep.sndIdle _ j m (Ne.symm hi)))
        (GSub.GNetStep.snd _ j m))
  | gdlv r i k m =>
    obtain rfl : ν = PMF.pure o :=
      (System.mapIdle_step_none (wccPull_gdlv r i k m) ν).mp hWs
    obtain ⟨hmem, hw⟩ := netStep_gdlv hn
    obtain rfl : w' = w := pureN_inj hw
    obtain ⟨hrr, hxid⟩ := stepN_gdlv_self (hall i)
    have hcol : (G r).1 i = (procs i).2 := by rw [← hrr]; exact hlive i
    have hx : x i = ((procs i).1, ((G r).1 i).deliverTo k m) := by
      rw [hcol]; exact pureN_inj hxid
    have hfor : ∀ i', i' ≠ i → x i' = procs i' := fun i' hi' =>
      pureN_inj (stepN_gdlv_foreign (Ne.symm hi') (hall i'))
    have hGfor : ∀ i' r', i' ≠ i →
        ((Function.update G r
          (Function.update ((G r).1) i (((G r).1 i).deliverTo k m), (G r).2)) r').1 i' =
            (G r').1 i' := by
      intro i' r' hi'
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hi' _ _
      · rw [Function.update_of_ne hr']
    have hown : ((Function.update G r
        (Function.update ((G r).1) i (((G r).1 i).deliverTo k m), (G r).2))
          (x i).1.proc.round).1 i = (x i).2 := by
      simp only [hx, hrr, Function.update_self]
    have hownf : ∀ r', (x i).1.proc.round < r' →
        ((Function.update G r
          (Function.update ((G r).1) i (((G r).1 i).deliverTo k m), (G r).2)) r').1 i =
            GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, hrr] at hr'
      rw [Function.update_of_ne (Nat.ne_of_gt hr')]
      exact hfut i r' (by rw [hrr]; exact hr')
    have howni : (x i).1.proc.input = none →
        (x i).1.proc.phase = Phase.idle ∧ (x i).1.proc.round = 0 := by
      simp only [hx]; exact hidle i
    have hxcore : ∀ i', (x i').1 = C i' := by
      intro i'
      by_cases hi' : i' = i
      · subst hi'; rw [hx]; exact hC i'
      · rw [hfor i' hi']; exact hC i'
    obtain ⟨h5, h6, h7⟩ := rel_one P i hlive hfut hidle hfor hGfor hown hownf howni
    exact match_round P rfl ((protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨hxcore, rfl, hA, fun r' => by rw [update_snd G r _ r']; exact hG r',
        h5, h6, h7⟩)
      (GSub.sub_event_step P r (GSub.GEvt.dlv i k m)
        (gprocs_family i _ (GSub.GProcStep.dlvRecv _ k m)
          (fun i' hi' => GSub.GProcStep.dlvIdle _ i k m (Ne.symm hi')))
        (GSub.GNetStep.dlv _ i k m (by rw [hG r]; exact hmem)))
  | dsnd j b =>
    obtain ⟨hdp, hw⟩ := netStep_dsnd hn
    obtain rfl : w' = w.dput j b := pureN_inj hw
    have hx : ∀ i, x i = procs i := by
      intro i
      by_cases hi : i = j
      · subst hi; exact pureN_inj (stepN_dsnd_self (hall i)).2
      · exact pureN_inj (stepN_dsnd_foreign (Ne.symm hi) (hall i))
    obtain ⟨h5, h6, h7⟩ := rel_none P (G' := G) hlive hfut hidle hx (fun _ _ => rfl)
    refine hvis (A' := A.dput j b) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by rw [hA]; simp [ANetState.dput, NetState.dput],
        fun r => by rw [hG r]; simp [NetState.dput], h5, h6, h7⟩)
      (gbcaSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ANetStep.dsnd A j b (by rw [hA]; exact hdp))
    rw [hCeq i, hx i]
    by_cases hi : i = j
    · subst hi; exact CoreProcStepN.dsndRelay _ b (stepN_dsnd_self (hall i)).1
    · exact CoreProcStepN.dsndIdle _ j b (Ne.symm hi)
  | ddlv i k b =>
    obtain ⟨hdp, hw⟩ := netStep_ddlv hn
    obtain rfl : w' = w := pureN_inj hw
    obtain ⟨hnotin, hxid⟩ := stepN_ddlv_self (hall i)
    have hx : x i = ((procs i).1.recvDec k b, (procs i).2) := pureN_inj hxid
    have hfor : ∀ i', i' ≠ i → x i' = procs i' := fun i' hi' =>
      pureN_inj (stepN_ddlv_foreign (Ne.symm hi') (hall i'))
    have hown : (G (x i).1.proc.round).1 i = (x i).2 := by
      simp only [hx, CoreRec.recvDec]; exact hlive i
    have hownf : ∀ r', (x i).1.proc.round < r' →
        (G r').1 i = GBCA.StageRec.initial P.n := by
      intro r' hr'; simp only [hx, CoreRec.recvDec] at hr'; exact hfut i r' hr'
    have howni : (x i).1.proc.input = none →
        (x i).1.proc.phase = Phase.idle ∧ (x i).1.proc.round = 0 := by
      simp only [hx, CoreRec.recvDec]; exact hidle i
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P i hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine hvis (A' := A) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩)
      (gbcaSide_idle P G hLne (by simp) not_false) (fun i' => ?_)
      (ANetStep.ddlv A i k b (by rw [hA]; exact hdp))
    by_cases hi' : i' = i
    · subst hi'; rw [hCeq i', hx]; exact CoreProcStepN.ddlvRecv _ k b hnotin
    · rw [hCeq i', hfor i' hi']; exact CoreProcStepN.ddlvIdle _ i k b (Ne.symm hi')
  | retWPub r id co b =>
    obtain rfl : w' = w.dput id b := pureN_inj (netStep_retWPub hn)
    obtain ⟨hph, hrr, hgr, hxid⟩ := stepN_retWPub_self (hall id)
    have hx : x id = ((procs id).1.stepRound co, GBCA.StageRec.initial P.n) :=
      pureN_inj hxid
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_retWPub_foreign (Ne.symm hi) (hall i))
    have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.stepRound, CoreRec.setProc]
      exact hfut id _ (Nat.lt_succ_self _)
    have hownf : ∀ r', (x id).1.proc.round < r' →
        (G r').1 id = GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, CoreRec.stepRound, CoreRec.setProc] at hr'
      exact hfut id r' (Nat.lt_of_succ_lt hr')
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon
      simp only [hx, CoreRec.stepRound, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine hvis (A' := A.dput id b) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by rw [hA]; simp [ANetState.dput, NetState.dput],
        fun r' => by rw [hG r']; simp [NetState.dput], h5, h6, h7⟩)
      (gbcaSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ANetStep.retWPub A r id co b)
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.retWPub _ r co b hph hrr hgr
    · rw [hCeq i, hfor i hi]
      exact CoreProcStepN.retWPubIdle _ r id co b (Ne.symm hi)
  | gcallLoop r id b =>
    obtain rfl : w' = w := pureN_inj (netStep_gcallLoop hn)
    obtain ⟨hph, hrr, hest, hxid⟩ := stepN_gcallLoop_self (hall id)
    have hx : x id = ((procs id).1.setProc { (procs id).1.proc with phase := .awaitG },
      (procs id).2) := pureN_inj hxid
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_gcallLoop_foreign (Ne.symm hi) (hall i))
    have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.setProc]; exact hlive id
    have hownf : ∀ r', (x id).1.proc.round < r' →
        (G r').1 id = GBCA.StageRec.initial P.n := by
      intro r' hr'; simp only [hx, CoreRec.setProc] at hr'; exact hfut id r' hr'
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon
      simp only [hx, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine hvis (A' := A) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩)
      (gbcaSide_owned_id P G r (by simp)
        (GSub.sub_lab_step P r (by simp)
          (fun i => GSub.GProcStep.callLoop _ id b)
          (GSub.GNetStep.gcallLoop _ id b))) (fun i => ?_)
      (ANetStep.gcallLoop A r id b)
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.gcallLoop _ r b hph hrr hest
    · rw [hCeq i, hfor i hi]
      exact CoreProcStepN.gcallLoopIdle _ r id b (Ne.symm hi)
  | byzCallG r k b => exact (stepN_byzCallG_dead (hall k)).elim
  | byzRetG r k out => exact (stepN_byzRetG_dead (hall k)).elim
  | byzCallGLoop r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzCallGLoop hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = procs i := fun i => pureN_inj (stepN_byzCallGLoop (hall i))
    obtain ⟨h5, h6, h7⟩ := rel_none P (G' := G) hlive hfut hidle hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩)
      (gbcaSide_owned_id P G r (by simp)
        (GSub.sub_lab_step P r (by simp)
          (fun i => GSub.GProcStep.byzCallLoop _ k b)
          (GSub.GNetStep.byzCallGLoop _ k b))) (fun i => ?_)
      (ANetStep.byzCallGLoop A r k b (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact CoreProcStepN.byzCallGLoopIdle _ r k b
  | byzCallW r k =>
    obtain ⟨hF, hw⟩ := netStep_byzCallW hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = procs i := fun i => pureN_inj (stepN_byzCallW (hall i))
    obtain ⟨h5, h6, h7⟩ := rel_none P (G' := G) hlive hfut hidle hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩)
      (gbcaSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ANetStep.byzCallW A r k (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact CoreProcStepN.byzCallWIdle _ r k
  | byzRetW r k b =>
    obtain ⟨hF, hw⟩ := netStep_byzRetW hn
    obtain rfl : w' = w := pureN_inj hw
    have hx : ∀ i, x i = procs i := fun i => pureN_inj (stepN_byzRetW (hall i))
    obtain ⟨h5, h6, h7⟩ := rel_none P (G' := G) hlive hfut hidle hx (fun _ _ => rfl)
    refine hvis (A' := A) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩)
      (gbcaSide_idle P G hLne (by simp) not_false) (fun i => ?_)
      (ANetStep.byzRetW A r k b (by rw [hA]; exact hF))
    rw [hCeq i, hx i]; exact CoreProcStepN.byzRetWIdle _ r k b

/-- The matching on a visible shared label. -/
theorem match_lab (P : Params) {procs : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ImplState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (procs, w, o) (G, C, A, o))
    {l : Lab P.n} (hl : l ≠ Lab.tau) {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (procs, w, o) (Sum.inl l) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      (composedGroup P).step (G, C, A, o) l (Ω.bind id) := by
  obtain ⟨hC, -, hA, hG, hlive, hfut, hidle⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  have hCeq : ∀ i, C i = (procs i).1 := fun i => (hC i).symm
  obtain ⟨x, w', ω, hall, hn, hOr, rfl⟩ := protocolPre_lab_inv P hl h
  have hWl : (wccLift P).step o (Sum.inl l) ω :=
    (System.mapIdle_step_some (wccPull_inl l) ω).mpr hOr
  have hLne : (Sum.inl l : NLab P.n) ≠ Silent.τ := by simpa using hl
  suffices hsuf : ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P))
        (prodPMF (PMF.pure x) (prodPMF (PMF.pure w') ω)) Ω ∧
      (composedPre P).step (G, C, A, o) (Sum.inl l) (Ω.bind id) by
    obtain ⟨Ω, hr, hs⟩ := hsuf
    exact ⟨Ω, hr, (composedGroup_step_iff P _ _ _).mpr (Or.inr hs)⟩
  cases l with
  | tau => exact absurd rfl hl
  | callABA id b =>
    obtain rfl : w' = w := pureN_inj (netStep_callABA hn)
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_callABA_foreign (Ne.symm hi) (hall i))
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.callABA id b)) (PMF.pure G) :=
      gbcaSide_idle P G hLne (by simp) not_false
    rcases stepN_callABA_own (hall id) with ⟨hin, hxid⟩ | hxid
    · have hx : x id = ((procs id).1.setProc { (procs id).1.proc with
          input := some b, est := some b, round := 0, phase := .toCallG },
          (procs id).2) := pureN_inj hxid
      have hr0 : (procs id).1.proc.round = 0 := (hidle id hin).2
      have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
        simp only [hx, CoreRec.setProc]
        rw [← hr0]; exact hlive id
      have hownf : ∀ r, (x id).1.proc.round < r →
          (G r).1 id = GBCA.StageRec.initial P.n := by
        intro r hr
        simp only [hx, CoreRec.setProc] at hr
        exact hfut id r (by rw [hr0]; exact hr)
      have howni : (x id).1.proc.input = none →
          (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
        intro hcon; simp [hx, CoreRec.setProc] at hcon
      obtain ⟨h5, h6, h7⟩ :=
        rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
      refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩) hGs (fun i => ?_)
        (ANetStep.callABAIdle A id b) hWl
      by_cases hi : i = id
      · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.input _ b hin
      · rw [hCeq i, hfor i hi]; exact CoreProcStepN.callABAIdle _ id b (Ne.symm hi)
    · have hx : ∀ i, x i = procs i := by
        intro i
        by_cases hi : i = id
        · subst hi; exact pureN_inj hxid
        · exact hfor i hi
      obtain ⟨h5, h6, h7⟩ := rel_none P hlive hfut hidle hx (fun _ _ => rfl)
      refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩) hGs (fun i => ?_)
        (ANetStep.callABAIdle A id b) hWl
      rw [hCeq i, hx i]
      by_cases hi : i = id
      · subst hi; exact CoreProcStepN.inputLoop _ b
      · exact CoreProcStepN.callABAIdle _ id b (Ne.symm hi)
  | retABA id b =>
    obtain ⟨hdp, hw⟩ := netStep_retABA hn
    obtain rfl : w' = w := pureN_inj hw
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_retABA_foreign (Ne.symm hi) (hall i))
    obtain ⟨hcnt, hret, hxid⟩ := stepN_retABA_own (hall id)
    have hx : x id =
        ((procs id).1.setProc { (procs id).1.proc with returned := true },
          (procs id).2) := pureN_inj hxid
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.retABA id b)) (PMF.pure G) :=
      gbcaSide_idle P G hLne (by simp) not_false
    have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.setProc]; exact hlive id
    have hownf : ∀ r, (x id).1.proc.round < r →
        (G r).1 id = GBCA.StageRec.initial P.n := by
      intro r hr; simp only [hx, CoreRec.setProc] at hr; exact hfut id r hr
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon; simp only [hx, CoreRec.setProc] at hcon ⊢; exact hidle id hcon
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩) hGs (fun i => ?_)
      (ANetStep.retABA A id b (by rw [hA]; exact hdp)) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.ret _ b hcnt hret
    · rw [hCeq i, hfor i hi]; exact CoreProcStepN.retABAIdle _ id b (Ne.symm hi)
  | callW r id =>
    obtain rfl : w' = w := pureN_inj (netStep_callW hn)
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_callW_foreign (Ne.symm hi) (hall i))
    obtain ⟨hph, hrr, hxid⟩ := stepN_callW_own (hall id)
    have hx : x id =
        ((procs id).1.setProc { (procs id).1.proc with phase := .awaitW },
          (procs id).2) := pureN_inj hxid
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.callW r id)) (PMF.pure G) :=
      gbcaSide_idle P G hLne (by simp) not_false
    have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.setProc]; exact hlive id
    have hownf : ∀ r', (x id).1.proc.round < r' →
        (G r').1 id = GBCA.StageRec.initial P.n := by
      intro r' hr'; simp only [hx, CoreRec.setProc] at hr'; exact hfut id r' hr'
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon; simp only [hx, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩) hGs (fun i => ?_)
      (ANetStep.callWIdle A r id) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.callW _ r hph hrr
    · rw [hCeq i, hfor i hi]; exact CoreProcStepN.callWIdle _ r id (Ne.symm hi)
  | retW r id co =>
    obtain rfl : w' = w := pureN_inj (netStep_retW hn)
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_retW_foreign (Ne.symm hi) (hall i))
    obtain ⟨hph, hrr, hgr, hxid⟩ := stepN_retW_own (hall id)
    have hx : x id = ((procs id).1.stepRound co, GBCA.StageRec.initial P.n) :=
      pureN_inj hxid
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.retW r id co)) (PMF.pure G) :=
      gbcaSide_idle P G hLne (by simp) not_false
    have hown : (G (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.stepRound, CoreRec.setProc]
      exact hfut id _ (Nat.lt_succ_self _)
    have hownf : ∀ r', (x id).1.proc.round < r' →
        (G r').1 id = GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, CoreRec.stepRound, CoreRec.setProc] at hr'
      exact hfut id r' (Nat.lt_of_succ_lt hr')
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon
      simp only [hx, CoreRec.stepRound, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ :=
      rel_one P id hlive hfut hidle hfor (fun _ _ _ => rfl) hown hownf howni
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, hG, h5, h6, h7⟩) hGs (fun i => ?_)
      (ANetStep.retWIdle A r id co) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.retW _ r co hph hrr hgr
    · rw [hCeq i, hfor i hi]; exact CoreProcStepN.retWIdle _ r id co (Ne.symm hi)
  | fail k =>
    obtain rfl : w' = NetState.corrupt P k w := pureN_inj (netStep_fail hn)
    have hx : ∀ i, x i = procs i := fun i => pureN_inj (stepN_fail (hall i))
    obtain ⟨h5, h6, h7⟩ := rel_none P (G' := fun r =>
      GSub.gAct P (Sum.inl (Lab.fail k)) (G r)) hlive hfut hidle hx
      (fun _ _ => by simp only [gAct_fail])
    have hrel : ∀ o' : ℕ → WCC.SpecState P.n,
        ProtocolRel P ((x, NetState.corrupt P k w, o') : ProtocolState P)
          (((fun r => GSub.gAct P (Sum.inl (Lab.fail k)) (G r)),
            (fun i => (x i).1), ANetState.corrupt P k A, o') : ComposedState P) := by
      intro o'
      refine (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨fun _ => rfl, rfl, ?_, ?_, h5, h6, h7⟩
      · rw [hA]; exact corrupt_anet w k
      · intro r
        simp only [gAct_fail]
        rw [hG r]
        exact corrupt_gnet w k r
    refine match_vis P hLne (fun o' _ => hrel o') (gbcaSide_fail P G k) (fun i => ?_)
      (ANetStep.fail A k) hWl
    rw [hCeq i, hx i]; exact CoreProcStepN.failIdle _ k
  | callG r id b =>
    obtain rfl : w' = w.gpool r id (.input b) := pureN_inj (netStep_callG hn)
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_callG_foreign (Ne.symm hi) (hall i))
    obtain ⟨hph, hrr, hest, hin, hxid⟩ := stepN_callG_own (hall id)
    have hx : x id = ((procs id).1.setProc { (procs id).1.proc with phase := .awaitG },
        (procs id).2.setP { (procs id).2.proc with
          input := some b,
          sentInput := Function.update (procs id).2.proc.sentInput b true }) :=
      pureN_inj hxid
    have hcol : (G r).1 id = (procs id).2 := by rw [← hrr]; exact hlive id
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.callG r id b))
        (PMF.pure (Function.update G r
          (Function.update ((G r).1) id (((G r).1 id).setP { ((G r).1 id).proc with
            input := some b,
            sentInput := Function.update ((G r).1 id).proc.sentInput b true }),
          ((G r).2).gpool id (.input b)))) :=
      gbcaSide_owned P G r (by simp)
        (GSub.sub_lab_step P r (by simp)
          (gprocs_family id _
            (GSub.GProcStep.call _ b (by rw [hcol]; exact hin))
            (fun i hi => GSub.GProcStep.callIdle _ id b (Ne.symm hi)))
          (GSub.GNetStep.callG _ id b))
    have hGfor : ∀ j r', j ≠ id →
        ((Function.update G r
          (Function.update ((G r).1) id (((G r).1 id).setP { ((G r).1 id).proc with
            input := some b,
            sentInput := Function.update ((G r).1 id).proc.sentInput b true }),
          ((G r).2).gpool id (.input b))) r').1 j = (G r').1 j := by
      intro j r' hj
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hj _ _
      · rw [Function.update_of_ne hr']
    have hown : ((Function.update G r
        (Function.update ((G r).1) id (((G r).1 id).setP { ((G r).1 id).proc with
          input := some b,
          sentInput := Function.update ((G r).1 id).proc.sentInput b true }),
        ((G r).2).gpool id (.input b))) (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.setProc, hrr, Function.update_self, hcol]
    have hownf : ∀ r', (x id).1.proc.round < r' →
        ((Function.update G r
          (Function.update ((G r).1) id (((G r).1 id).setP { ((G r).1 id).proc with
            input := some b,
            sentInput := Function.update ((G r).1 id).proc.sentInput b true }),
          ((G r).2).gpool id (.input b))) r').1 id =
            GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, CoreRec.setProc, hrr] at hr'
      rw [Function.update_of_ne (Nat.ne_of_gt hr')]
      exact hfut id r' (by rw [hrr]; exact hr')
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon
      simp only [hx, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ := rel_one P id hlive hfut hidle hfor hGfor hown hownf howni
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, by simpa using hA, rel_gpool hG r id (.input b) _,
        h5, h6, h7⟩) hGs (fun i => ?_) (ANetStep.callGIdle A r id b) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.callG _ r b hph hrr hest
    · rw [hCeq i, hfor i hi]; exact CoreProcStepN.callGIdle _ r id b (Ne.symm hi)
  | retG r id out =>
    obtain rfl : w' = w := pureN_inj (netStep_retG hn)
    have hfor : ∀ i, i ≠ id → x i = procs i := fun i hi =>
      pureN_inj (stepN_retG_foreign (Ne.symm hi) (hall i))
    have hstage : ∃ hph : (procs id).1.proc.phase = Phase.awaitG,
        (procs id).1.proc.round = r ∧
        GSub.GProcStep P r id ((G r).1 id) (Sum.inl (Sum.inl (Lab.retG r id out)))
          (PMF.pure (((G r).1 id).setP { ((G r).1 id).proc with returned := true })) ∧
        x id = ((procs id).1.setProc { (procs id).1.proc with
          est := out.est, lastGrade := some out, phase := .toCallW },
          (procs id).2.setP { (procs id).2.proc with returned := true }) := by
      have hcolr : ∀ (hrr : (procs id).1.proc.round = r), (G r).1 id = (procs id).2 :=
        fun hrr => by rw [← hrr]; exact hlive id
      cases out with
      | A v =>
        obtain ⟨hph, hrr, hcnt, hret, hxid⟩ := stepN_retG_A_own (hall id)
        exact ⟨hph, hrr, GSub.GProcStep.retA _ v (by rw [hcolr hrr]; exact hcnt)
          (by rw [hcolr hrr]; exact hret), pureN_inj hxid⟩
      | B v =>
        obtain ⟨hph, hrr, hcnt, honce, hbind, hval, hret, hxid⟩ :=
          stepN_retG_B_own (hall id)
        exact ⟨hph, hrr, GSub.GProcStep.retB _ v (by rw [hcolr hrr]; exact hcnt)
          (by rw [hcolr hrr]; exact honce) (by rw [hcolr hrr]; exact hbind)
          (by rw [hcolr hrr]; exact hval) (by rw [hcolr hrr]; exact hret),
          pureN_inj hxid⟩
      | C =>
        obtain ⟨hph, hrr, hcnt, hval, hret, hxid⟩ := stepN_retG_C_own (hall id)
        exact ⟨hph, hrr, GSub.GProcStep.retC _ (by rw [hcolr hrr]; exact hcnt)
          (by rw [hcolr hrr]; exact hval) (by rw [hcolr hrr]; exact hret),
          pureN_inj hxid⟩
    obtain ⟨hph, hrr, hrow, hx⟩ := hstage
    have hcol : (G r).1 id = (procs id).2 := by rw [← hrr]; exact hlive id
    have hGs : (GSub.gbcaSide P).step G (Sum.inl (Lab.retG r id out))
        (PMF.pure (Function.update G r
          (Function.update ((G r).1) id
            (((G r).1 id).setP { ((G r).1 id).proc with returned := true }),
          (G r).2))) :=
      gbcaSide_owned P G r (by simp)
        (GSub.sub_lab_step P r (by simp)
          (gprocs_family id _ hrow
            (fun i hi => GSub.GProcStep.retIdle _ id out (Ne.symm hi)))
          (GSub.GNetStep.retGIdle _ id out))
    have hGfor : ∀ j r', j ≠ id →
        ((Function.update G r
          (Function.update ((G r).1) id
            (((G r).1 id).setP { ((G r).1 id).proc with returned := true }),
          (G r).2)) r').1 j = (G r').1 j := by
      intro j r' hj
      by_cases hr' : r' = r
      · subst hr'; rw [Function.update_self]; exact Function.update_of_ne hj _ _
      · rw [Function.update_of_ne hr']
    have hown : ((Function.update G r
        (Function.update ((G r).1) id
          (((G r).1 id).setP { ((G r).1 id).proc with returned := true }),
        (G r).2)) (x id).1.proc.round).1 id = (x id).2 := by
      simp only [hx, CoreRec.setProc, hrr, Function.update_self, hcol]
    have hownf : ∀ r', (x id).1.proc.round < r' →
        ((Function.update G r
          (Function.update ((G r).1) id
            (((G r).1 id).setP { ((G r).1 id).proc with returned := true }),
          (G r).2)) r').1 id = GBCA.StageRec.initial P.n := by
      intro r' hr'
      simp only [hx, CoreRec.setProc, hrr] at hr'
      rw [Function.update_of_ne (Nat.ne_of_gt hr')]
      exact hfut id r' (by rw [hrr]; exact hr')
    have howni : (x id).1.proc.input = none →
        (x id).1.proc.phase = Phase.idle ∧ (x id).1.proc.round = 0 := by
      intro hcon
      simp only [hx, CoreRec.setProc] at hcon
      simp [(hidle id hcon).1] at hph
    obtain ⟨h5, h6, h7⟩ := rel_one P id hlive hfut hidle hfor hGfor hown hownf howni
    refine match_vis P hLne (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
      ⟨fun _ => rfl, rfl, hA, fun r' => by
        rw [update_snd G r _ r']; exact hG r', h5, h6, h7⟩) hGs (fun i => ?_)
      (ANetStep.retGIdle A r id out) hWl
    by_cases hi : i = id
    · subst hi; rw [hCeq i, hx]; exact CoreProcStepN.retG _ r out hph hrr
    · rw [hCeq i, hfor i hi]; exact CoreProcStepN.retGIdle _ r id out (Ne.symm hi)

/-- The matching on the silent label. -/
theorem match_tau (P : Params) {procs : ∀ _ : Fin P.n, ProcRec P.n}
    {w : NetState P.n} {o : ℕ → WCC.SpecState P.n}
    {G : ℕ → GBCA.ImplState P.n} {C : ∀ _ : Fin P.n, CoreRec P.n}
    {A : ANetState P.n} (hR : ProtocolRel P (procs, w, o) (G, C, A, o))
    {μ : PMF (ProtocolState P)}
    (h : (protocolPre P).step (procs, w, o) (Sum.inl Lab.tau) μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
      (composedGroup P).step (G, C, A, o) Lab.tau (Ω.bind id) := by
  obtain ⟨hC, -, hA, hG, hlive, hfut, hidle⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  rcases protocolPre_tau_inv P h with ⟨w', hn, rfl⟩ | ⟨ω, hW, rfl⟩
  · rcases netStep_tau hn with ⟨r, k, m, hF, hw⟩ | ⟨k, b, hF, hw⟩
    · obtain rfl : w' = w.gpool r k m := pureN_inj hw
      have hFG : k ∈ ((G r).2).F := by rw [hG r]; exact hF
      have hfst := update_fst G r (X := ((G r).1, ((G r).2).gpool k m)) rfl
      have hrel' : ProtocolRel P ((procs, w.gpool r k m, o) : ProtocolState P)
          ((Function.update G r ((G r).1, ((G r).2).gpool k m), C, A, o) :
            ComposedState P) := by
        refine (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, by simpa using hA, ?_, ?_, ?_, hidle⟩
        · intro r'
          by_cases hr : r' = r
          · subst hr
            rw [Function.update_self]
            change ((G r').2).gpool k m = _
            rw [hG r']
            simp [GSub.GNetState.gpool]
          · rw [Function.update_of_ne hr, hG r', gpool_pool_ne w r k m hr]
            simp
        · intro j; rw [hfst]; exact hlive j
        · intro j r' hr'; rw [hfst]; exact hfut j r' hr'
      obtain ⟨Ω, hrel, hbind⟩ := match_pure P hrel'
      refine ⟨Ω, hrel, ?_⟩
      rw [hbind]
      exact composedGroup_of_tau P (composedPre_tau_gbca P (gbcaSide_tau P G r
        (GSub.sub_tau_net P r (GSub.GNetStep.byzG _ k m hFG))))
    · obtain rfl : w' = w.dput k b := pureN_inj hw
      have hFA : k ∈ A.F := by rw [hA]; exact hF
      have hrel' : ProtocolRel P ((procs, w.dput k b, o) : ProtocolState P)
          ((G, C, A.dput k b, o) : ComposedState P) := by
        refine (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, ?_, ?_, hlive, hfut, hidle⟩
        · rw [hA]; simp [ANetState.dput, NetState.dput]
        · intro r; rw [hG r]; simp [NetState.dput]
      obtain ⟨Ω, hrel, hbind⟩ := match_pure P hrel'
      refine ⟨Ω, hrel, ?_⟩
      rw [hbind]
      exact composedGroup_of_tau P (composedPre_tau_aNet P (ANetStep.byzD A k b hFA))
  · obtain ⟨Ω, hrel, hbind⟩ := match_prod P (x := procs) (w := w) (G := G) (C := C)
      (A := A) (ν := ω) (fun o' _ => (protocolRel_mk P _ _ _ _ _ _ _).mpr
        ⟨hC, rfl, hA, hG, hlive, hfut, hidle⟩)
    refine ⟨Ω, hrel, ?_⟩
    rw [hbind]
    exact composedGroup_of_tau P (composedPre_tau_wcc P hW)

/-! ### The simulation -/

/-- The matching at the group level: the rendezvous alphabet is hidden on both
sides, so a hidden protocol rendezvous is answered by a silent transition of
the composed group. -/
theorem match_group (P : Params) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P u t) {l : Lab P.n} {μ : PMF (ProtocolState P)}
    (h : (protocolGroup P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧ (composedGroup P).step t l (Ω.bind id) := by
  obtain ⟨procs, w, o⟩ := u
  obtain ⟨G, C, A, o'⟩ := t
  obtain ⟨hC, ho, hA, hG, hlive, hfut, hidle⟩ := (protocolRel_mk P _ _ _ _ _ _ _).mp hR
  subst ho
  have hR : ProtocolRel P (procs, w, o) (G, C, A, o) :=
    (protocolRel_mk P _ _ _ _ _ _ _).mpr ⟨hC, rfl, hA, hG, hlive, hfut, hidle⟩
  rcases (protocolGroup_step_iff P _ _ _).mp h with ⟨rfl, e, hstep⟩ | hstep
  · exact match_event P hR e hstep
  · by_cases hl : l = Lab.tau
    · subst hl; exact match_tau P hR hstep
    · exact match_lab P hR hl hstep

/-- The matching at the system level: a hidden sub-protocol label is silent on
both sides, and every other label is answered on the nose. -/
theorem match_step (P : Params) {u : ProtocolState P} {t : ComposedState P}
    (hR : ProtocolRel P u t) {l : Lab P.n} {μ : PMF (ProtocolState P)}
    (h : (protocol P).step u l μ) :
    ∃ Ω : PMF (PMF (ComposedState P)),
      PMFRel (diracRel (ProtocolRel P)) μ Ω ∧
        ((l = Silent.τ ∧ weakTau (composed P) (PMF.pure t) (Ω.bind id)) ∨
         (¬ (l = Silent.τ) ∧ weakStep (composed P) (PMF.pure t) l (Ω.bind id))) := by
  rcases (protocol_step_iff P u l μ).mp h with ⟨rfl, l', hmem, hg⟩ | ⟨hnm, hg⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    exact ⟨Ω, hrel, Or.inl ⟨rfl, weakTau_of_step rfl
      ((System.abstract_step _ _ _ _ _).mpr (Or.inl ⟨rfl, l', hmem, hlay⟩))⟩⟩
  · obtain ⟨Ω, hrel, hlay⟩ := match_group P hR hg
    have hstep : (composed P).step t l (Ω.bind id) :=
      (System.abstract_step _ _ _ _ _).mpr (Or.inr ⟨hnm, hlay⟩)
    by_cases hτ : l = Silent.τ
    · exact ⟨Ω, hrel, Or.inl ⟨hτ, weakTau_of_step hτ hstep⟩⟩
    · exact ⟨Ω, hrel, Or.inr ⟨hτ, weakStep_strong hstep⟩⟩

/-- The two initial states are related: everything is initial, so the live
column is the initial stage record and every column above round `0` is
pristine. -/
theorem protocolRel_init (P : Params) : ProtocolRel P (protocol P).init (composed P).init :=
  ⟨fun _ => rfl, rfl, rfl, fun _ => rfl, fun _ => rfl, fun _ _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩⟩

/-- **The protocol forward-simulates into its composed reading**
along the Dirac lift of `ProtocolRel`. -/
theorem protocolSim (P : Params) :
    ProbabilisticForwardSimulation (protocol P) (composed P) (diracRel (ProtocolRel P)) where
  init := ⟨PMF.pure (composed P).init,
    fun _ hs => by rwa [PMF.mem_support_pure_iff] at hs,
    (composed P).init, rfl, protocolRel_init P⟩
  step := by
    rintro s_C μ_A ⟨t, rfl, hR⟩ l μ_C hstep
    exact match_step P hR hstep

/-- **The composition inclusion**: every trace distribution the protocol
achieves is achieved by its composed reading. -/
theorem protocol_composed (P : Params) :
    achievableTraceDists (protocol P) ⊆ achievableTraceDists (composed P) :=
  (protocolSim P).achievableTraceDists_subset

/-! ### Mechanical axiom firewall

The composition step of the chain may not acquire a `sorryAx` dependence. -/

/-- info: 'PLTS.ABA.protocol_composed' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms protocol_composed

end ABA
end PLTS
