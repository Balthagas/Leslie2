# Composition — why the chain is cut where it is

The ABA case study relates the protocol as it runs to a small specification through
four systems:

```
protocol  ⊑  composed  ⊑  hybrid  ⊑  ABA.spec
```

`protocol` is what runs: `n` corruption-blind programs beside a network adversary and a
coin oracle. `composed` is the same protocol read as a composition of components.
`hybrid` replaces each round's graded-agreement subsystem by the graded agreement
specification. `ABA.spec` is the single-automaton reading of agreement.

This note records why that cut is placed where it is, what it buys, and what the model
already weakens. The systems themselves are in `ABA/Protocol.lean`, `ABA/Spec.lean` and
`ABA/Hybrid.lean`, which carries both `composed` and `hybrid`, over the components of
`ABA/Components.lean`; the first link is in `ABA/ProtocolSim.lean`. The file guide is
`ABA/README.md`.

The first link is where the chain passes from implementation to specification: `protocol`
is the system that runs, and everything above it is specification. It is therefore an
inclusion, `ProtocolSim.protocol_composed`, and not an equality. A process node of the
protocol carries one graded-agreement stage record, that of the round its round loop is
in, and the round advance resets it (D20); a composed state carries one graded-agreement
subsystem per round at every moment. The stage records of the rounds a process has left
are specification-side state, so `ProtocolRel` relates the two readings rather than
mapping one onto the other.

## What the composition buys

A sub-protocol is swappable exactly when its factor boundary owns its network.

Giving each round its own message fabric is what makes the round a factor, and a factor
can be replaced. The substitution is one family congruence and one parallel
precongruence, then `abstract`, `relabel`, `abstract` to run the composition pipeline
out. Nothing else in the chain is touched.

That is a modular axis rather than a one-off. Varying the power of the message fabric —
losses, reordering, a different forgery model — is a change inside the round subsystem,
swapped in by the same precongruence.

Idealizing the round also exposes an asymmetry worth naming. The round's pools, its
delivery guards and its injections die with the graded-agreement idealization. The
DECIDED pools, the corruption budget and the authorisation `k ∈ F` of every Byzantine
drive survive it, at the ABA-side network. What a component owns is what disappears with
it.

## Where each network is external

Two networks carry the protocol. Neither is internal to a process, and neither is a
field of a record.

The round's message fabric `GSub.gNet` is a factor of `composed` and of `hybrid`, and it
disappears at the substitution, inside the factor that is exchanged. It is also the
second factor of `GBCA.ImplState`, the state the round refinement is defined on.

The ABA-side DECIDED network `Comp.aNet` is a factor of every system in the chain, and
the second factor of `ABAState`, the state `coreRel` is defined on.

Both invariants therefore read their network through accessors on a pair — the
`GBCA.ImplState` accessors in `ABA/GBCAImpl.lean`, the `ABAState` accessors in
`ABA/ABAState.lean` — and name the network's own pools rather than a copy of them held
inside a record. Weakening either network is a change to that one factor.

## Every state is a component's own record or a product of them

The property holds across the development, and a reader should not have to re-derive it.

Each leaf record holds exactly one box's data: `ProcCore` and `CoreRec` for a round loop,
`GBCA.ProcState` and `GBCA.StageRec` for a graded-agreement stage, `GSub.GNetState` for a
round's fabric, `Comp.ANetState` for the DECIDED network, and one `SpecState` for each of
the three specifications. Each composite state is an explicit product of those:
`Net.ProcRec`, `GBCA.ImplState`, `ABAState`, `Comp.ComposedState`, `HybridState`.

One record holds two kinds of message pool at once, and it is the right one to.
`Net.NetState` (`ABA/Protocol.lean`) carries the stage pools, the DECIDED pools and the
corrupted set together, because it is the network adversary of the protocol — the subject
of the chain, not a vehicle for proving anything about it.
`ProtocolSim.protocol_composed` carries that reading into one where each round owns a
fabric beside `Comp.ANetState`, and every step above the first link runs there.

## What the DECIDED model already weakens

The ABA-side network is the one the chain never idealizes, so what it assumes is what the
development assumes. Much of the weakening one might ask for is already in it.

`dpool` is a `Finset`, so there is no delivery order to disturb. Receipts are sets too and
`CoreRec.recvDec` files by insertion, so a repeated delivery of one (receiver, sender,
bit) triple carries no information: `Comp.ANetStep.ddlv` consumes nothing, and the
receiver's `Comp.CoreProcStepN.ddlvRecv` declines the repeat under `b ∉ decIn k` rather
than taking a step that would change no state. Duplication is immaterial here, not assumed
away.

No rule forces a delivery, so any subset of the multicasts may be lost. `byzD` injects
either bit for any `k ∈ F`, so a corrupted process may equivocate in the DECIDED pools.

What remains assumed is unforgeability of an honest process's DECIDED multicast. The
delivery guard `b ∈ dpool j` attributes every receipt to a genuine send by the named
sender, and no rule lets one process pool under another's name.
