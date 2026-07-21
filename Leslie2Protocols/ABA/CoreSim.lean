/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2Protocols.ABA.CoreSimRel
import Leslie2Protocols.ABA.CoreSimBurst

/-!
# The core simulation `hybridSpec ⊑ ABA.spec` (M6-E2, design v2.2)

Assembles `CoreSimRel`'s invariant/relation and `CoreSimBurst`'s burst kit into the theorem
`coreSim`, the probabilistic forward simulation `hybridSpec P ⊑ spec P` along `coreRel P`.
-/

namespace PLTS
namespace ABA

variable {P : Params}

/-- The core simulation relation, `Dirac`-lifted: every concrete state relates to the point
mass on its (unique) abstract twin. -/
def coreRel (P : Params) : HState P → PMF (SpecState P.n) → Prop :=
  diracRel (coreR P)

/-- **Stutter-row packaging.** If every post-state `s'` in the support of a concrete τ-step's
outcome `μ_C` relates to the *same* abstract state `a` (via `coreR`), the abstract twin can
answer with the trivial `weakTau_refl` stutter: the coupling `Ω := μ_C.map (fun s' => (s', pure
a))` has first marginal `μ_C` and second marginal the constant `pure (pure a)` (`PMF.map_const`),
so `ω := pure (pure a)` and `ω.bind id = pure a` (`PMF.pure_bind`). Reused by every hidden
handshake / internal row and by the unanimous `bindSet` / stale coin-flip cases. -/
private theorem stutter_step {P : Params} (μ_C : PMF (HState P)) (a : SpecState P.n)
    (hA : ∀ s' ∈ μ_C.support, coreR P s' a) :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) μ_C ω ∧ weakTau (spec P) (PMF.pure a) (ω.bind id) := by
  set Ω : PMF (HState P × PMF (SpecState P.n)) := μ_C.map (fun s' => (s', PMF.pure a)) with hΩdef
  have hFst : Ω.map Prod.fst = μ_C := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.fst ∘ fun s' => (s', PMF.pure a)) = (id : HState P → HState P) := rfl
    rw [hcomp, PMF.map_id]
  have hSnd : Ω.map Prod.snd = PMF.pure (PMF.pure a) := by
    rw [hΩdef, PMF.map_comp]
    have hcomp : (Prod.snd ∘ fun s' => (s', PMF.pure a)) =
        (Function.const (HState P) (PMF.pure a)) := rfl
    rw [hcomp, PMF.map_const]
  refine ⟨PMF.pure (PMF.pure a), ⟨Ω, hFst, hSnd, ?_⟩, ?_⟩
  · intro p hp
    rw [hΩdef, PMF.mem_support_map_iff] at hp
    obtain ⟨s', hs', hp'⟩ := hp
    rw [← hp']
    exact ⟨a, rfl, hA s' hs'⟩
  · rw [PMF.pure_bind]
    exact weakTau_refl _ _

/-- A `weakTau` burst followed by a genuine (possibly visible) single step, in `weakStep`'s other
associativity: the burst happens *after* the visible step (needed for `callABA`'s bank-then-
rebind row, where the visible `rule 1` fires first and the `rule 4` τ-tail follows). -/
theorem weakStep_of_step_then_burst {a a' a'' : SpecState P.n} {l : Lab P.n}
    (hstep : SpecStep P a l (PMF.pure a'))
    (hburst : weakTau (spec P) (PMF.pure a') (PMF.pure a'')) :
    weakStep (spec P) (PMF.pure a) l (PMF.pure a'') :=
  ⟨PMF.pure a, PMF.pure a', weakTau_refl _ _, hyperStep_pure_of_step hstep, hburst⟩

/-- Abstract-side corruption (deviation D1) only ever touches `F`. -/
theorem SpecState.corrupt_ret {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).ret = s.ret := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_call {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).call = s.call := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_bind {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).bind = s.bind := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_val {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).val = s.val := by unfold SpecState.corrupt; split <;> rfl

theorem SpecState.corrupt_coin {P : Params} (id : Fin P.n) (s : SpecState P.n) :
    (s.corrupt P id).coin = s.coin := by unfold SpecState.corrupt; split <;> rfl

/-- Corruption of `F` is monotone (`fail`'s guard only ever inserts). -/
theorem CoreState.corrupt_F_subset {P : Params} (c : CoreState P.n) (id : Fin P.n) :
    c.F ⊆ (c.corrupt P id).F := by
  unfold CoreState.corrupt; split_ifs with hcond
  · exact Finset.subset_insert _ _
  · exact Finset.Subset.refl _

/-- None of `Abs`'s seven fields mention `w`: the abstract twin never fires rule 5, so it is
completely insensitive to the WCC family's state (v2.2). -/
theorem Abs.w_irrelevant {P : Params} {g : ℕ → GBCA.SpecState P.n} {c : CoreState P.n}
    {w w' : ℕ → WCC.SpecState P.n} {a : SpecState P.n} (hA : Abs P g c w a) :
    Abs P g c w' a :=
  ⟨hA.F_eq, hA.ret_eq, hA.call_pre, hA.call_post, hA.coin_bot, hA.val_cert, hA.bind_ready⟩

/-- A triple product of Dirac PMFs collapses to a single Dirac (used to normalise the concrete
outcome of every visible row, `prodPMF (pure g) (prodPMF (pure c) (pure w))`, into `dirac_step`'s
expected `PMF.pure` shape). -/
private theorem prodPMF_pure_pure_pure {α β γ : Type*} (x : α) (y : β) (z : γ) :
    prodPMF (PMF.pure x) (prodPMF (PMF.pure y) (PMF.pure z)) = PMF.pure (x, (y, z)) := by
  simp [prodPMF, PMF.pure_bind]

/-- The full-`call` row always meets the quorum guard (re-derived locally: `CoreSimBurst`'s copy
is `private`). -/
private theorem quorum_of_full_call' {P : Params} {s : SpecState P.n}
    (hcall : ∀ id, s.call id ≠ none) : s.quorum P := by
  have heq : (Finset.univ.filter (fun id => id ∉ s.F ∧ s.call id ≠ none)) ∪ s.F
      = (Finset.univ : Finset (Fin P.n)) := by
    ext id
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : id ∈ s.F
    · simp [h]
    · simp [h, hcall id]
  unfold SpecState.quorum
  rw [heq, Finset.card_univ, Fintype.card_fin]
  omega

/-- Like `CoreSimBurst.val_force`, but decoupled from the pre-existing bind value: since the
abstract twin never fires rule 5 (`coin_bot`), `TVal.agrees` is always `False`, so `fill_chain`'s
`havail` hypothesis is vacuous regardless of *which* bit `a.bind` already carries — only
`a.bind ≠ none` matters, letting the closing `rebind_unanim (b := !b)` overwrite it to `some b`
outright. -/
private theorem val_force' {P : Params} {a : SpecState P.n} {b vb : Bool}
    (hbind : a.bind = some vb) (hcall : ∀ id, a.call id = none) (hcoin : a.coin = .bot)
    (hval : a.val = none ∨ a.val = some b) :
    ∃ a' : SpecState P.n, weakTau (spec P) (PMF.pure a) (PMF.pure a') ∧
      a'.val = some b ∧ a'.bind = some b ∧ a'.call = (fun _ => none) ∧
      a'.ret = a.ret ∧ a'.F = a.F ∧ a'.coin = .bot := by
  set a1 : SpecState P.n := { a with call := fun _ => some b } with ha1def
  have hfill : weakTau (spec P) (PMF.pure a) (PMF.pure a1) := by
    refine fill_chain hbind (t := fun _ => some b) ?_ ?_ hcall
    · intro id b' hb'
      have hbeq : b = b' := Option.some_inj.mp hb'
      rw [← hbeq]; exact hval
    · intro hagree
      exfalso; rw [hbind, hcoin] at hagree
      cases vb <;> simp [TVal.agrees] at hagree
  have ha1quorum : a1.quorum P := quorum_of_full_call' (s := a1) (fun id => by simp [ha1def])
  have ha1avoid : ∀ id, id ∉ a1.F → a1.call id ≠ some (!b) := by
    intro id _
    simp only [ha1def]
    intro hcontra
    exact absurd (Option.some_inj.mp hcontra) (by cases b <;> simp)
  have hreb := rebind_unanim (a := a1) (b := !b) ha1quorum ha1avoid
  rw [Bool.not_not] at hreb
  exact ⟨_, weakTau_trans hfill hreb, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- **Visible-row packaging.** A single concrete Dirac outcome `s_C'` matched by a single
abstract state `a'` (`coreR`-related) closes the `weakStep` disjunct of the simulation clause:
the coupling is the Dirac-of-Dirac `ω := pure (pure a')`, whose `bind id` collapses back to
`pure a'` (`PMF.pure_bind`), so any `weakStep (spec P) (pure a) l (pure a')` transfers directly. -/
private theorem dirac_step {P : Params} (s_C' : HState P) (a' : SpecState P.n)
    (hcoreR : coreR P s_C' a') :
    ∃ ω : PMF (PMF (SpecState P.n)),
      PMFRel (coreRel P) (PMF.pure s_C') ω ∧ ω.bind id = PMF.pure a' := by
  refine ⟨PMF.pure (PMF.pure a'), ⟨PMF.pure (s_C', PMF.pure a'), ?_, ?_, ?_⟩, ?_⟩
  · rw [PMF.pure_map]
  · rw [PMF.pure_map]
  · intro p hp; rw [PMF.mem_support_pure_iff] at hp; subst hp; exact ⟨a', rfl, hcoreR⟩
  · rw [PMF.pure_bind]; rfl

/-- A hidden-API label can never be visible at the `hybridSpec` level (it is always relabeled to
`τ` by `.abstract`), so any purported `hybridSpec`-step carrying one is vacuous. -/
private theorem hidden_label_impossible {P : Params} {s_C : HState P} {l : Lab P.n}
    {μ_C : PMF (HState P)} (hmem : l ∈ Lab.hiddenAPI P.n) (hne : l ≠ Silent.τ)
    (hstep : (hybridSpec P).step s_C l μ_C) : False := by
  unfold hybridSpec at hstep
  rw [System.abstract_step] at hstep
  rcases hstep with ⟨h, -⟩ | ⟨h, -⟩
  · exact hne h
  · exact h hmem

/-- **The core simulation.** `hybridSpec P` is a probabilistic forward simulation of `spec P`
along `coreRel P` (design v2.2, the never-flipping abstract twin). -/
theorem coreSim (P : Params) :
    ProbabilisticForwardSimulation (hybridSpec P) (spec P) (coreRel P) := by
  refine ⟨⟨PMF.pure (SpecState.initial P.n), ?_, SpecState.initial P.n, rfl, Inv.initial P,
    Abs.initial P⟩, ?_⟩
  · intro s_A hs_A; rw [PMF.mem_support_pure_iff] at hs_A; exact hs_A
  · intro s_C μ_A hR l μ_C hstep
    obtain ⟨g, c, w⟩ := s_C
    obtain ⟨a, rfl, hI, hAbs⟩ := hR
    dsimp only at hI hAbs
    cases l with
    | tau =>
      rcases hybrid_step_tau P g c w μ_C hstep with
        ⟨r, μr, hstepG, rfl⟩ | ⟨μc, hstepC, rfl⟩ | ⟨r, μw', hstepW, rfl⟩ |
        ⟨r, id, b, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, out, bound, μr, μc, hstepG, hstepC, rfl⟩ |
        ⟨r, id, μw', μc, hstepW, hstepC, rfl⟩ | ⟨r, id, b, μw', μc, hstepW, hstepC, rfl⟩
      · -- row 3: `bindSet` (`gbcaTau`).  v2.2 amendment: the abstract twin bursts (rule 4)
        -- exactly when it is still unbound and the honest banked inputs are genuinely mixed;
        -- otherwise it stutters (`Abs.step_gbcaTau`, unanimity supplied through `hUnan`).
        by_cases hmix : a.bind = none ∧
            (∃ id, id ∉ c.F ∧ (c.procs id).input = some true) ∧
            (∃ id, id ∉ c.F ∧ (c.procs id).input = some false)
        · -- mixed honest inputs while unbound: rule-4 burst at this row
          obtain ⟨hbindNone, ⟨idT, hidTF, hidTin⟩, ⟨idF, hidFF, hidFin⟩⟩ := hmix
          cases hstepG with
          | bindSet b hq hw hbg =>
            set g' := Function.update g r { g r with bind := some b } with hg'def
            have hμ : prodPMF ((PMF.pure ({ g r with bind := some b } : GBCA.SpecState P.n)).map
                (Function.update g r)) (PMF.pure (c, w)) = PMF.pure (g', (c, w)) := by
              rw [PMF.pure_map, ← hg'def]; simp [prodPMF, PMF.pure_bind]
            have hmem : (g', (c, w)) ∈ (prodPMF
                ((PMF.pure ({ g r with bind := some b } : GBCA.SpecState P.n)).map
                  (Function.update g r)) (PMF.pure (c, w))).support := by
              rw [hμ]; simp
            have hI' : Inv P g' c w := hI.step hstep hmem
            have hqA : a.quorum P := by
              unfold GBCA.SpecState.quorum at hq
              refine le_trans hq (Finset.card_le_card ?_)
              intro x hx
              simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
              rcases hx with ⟨hxF, hxc⟩ | hxF
              · have hxc' : x ∉ c.F := (hI.F_g r) ▸ hxF
                refine Or.inl ⟨by rw [hAbs.F_eq]; exact hxc', ?_⟩
                rw [hAbs.call_pre hbindNone x]; exact hI.input_called r x hxc' hxc
              · exact Or.inr (by rw [hAbs.F_eq, ← hI.F_g r]; exact hxF)
            have h1 : ∃ i, i ∉ a.F ∧ a.call i = some true :=
              ⟨idT, by rw [hAbs.F_eq]; exact hidTF,
                by rw [hAbs.call_pre hbindNone idT]; exact hidTin⟩
            have h0 : ∃ i, i ∉ a.F ∧ a.call i = some false :=
              ⟨idF, by rw [hAbs.F_eq]; exact hidFF,
                by rw [hAbs.call_pre hbindNone idF]; exact hidFin⟩
            set a2 : SpecState P.n :=
              { a with call := fun _ => none, bind := some b, coin := .bot } with ha2def
            have hburst : weakTau (spec P) (PMF.pure a) (PMF.pure a2) :=
              weakTau_of_step rfl (SpecStep.mixed a b hqA h1 h0)
            have hAbs2 : Abs P g' c w a2 := by
              refine ⟨hAbs.F_eq, hAbs.ret_eq, ?_, ?_, ?_, ?_, ?_⟩
              · intro h; exact absurd h (by rw [ha2def]; simp)
              · intro _ id'; rw [ha2def]
              · rw [ha2def]
              · intro v hv
                obtain ⟨r0, hg0, hb0⟩ := hAbs.val_cert v (by rw [ha2def] at hv; exact hv)
                have hr0 : r0 ≠ r := by rintro rfl; rw [hbg] at hb0; exact absurd hb0 (by simp)
                exact ⟨r0, by rw [hg'def, Function.update_of_ne hr0]; exact hg0,
                  by rw [hg'def, Function.update_of_ne hr0]; exact hb0⟩
              · intro h; exact absurd h (by rw [ha2def]; simp)
            rw [hμ]
            obtain ⟨ω, hRel, hbid⟩ := dirac_step (g', c, w) a2 ⟨hI', hAbs2⟩
            refine ⟨ω, hRel, Or.inl ⟨rfl, ?_⟩⟩
            rw [hbid]; exact hburst
        · -- unanimous-or-none (or already bound): stutter via `Abs.step_gbcaTau`
          have hUnan : a.bind = none → ∀ id id' bb bb', id ∉ c.F → id' ∉ c.F →
              (c.procs id).input = some bb → (c.procs id').input = some bb' → bb = bb' := by
            intro hbn id id' bb bb' hf hf' hin hin'
            by_contra hne
            apply hmix
            cases bb <;> cases bb'
            · exact absurd rfl hne
            · exact ⟨hbn, ⟨id', hf', hin'⟩, ⟨id, hf, hin⟩⟩
            · exact ⟨hbn, ⟨id, hf, hin⟩, ⟨id', hf', hin'⟩⟩
            · exact absurd rfl hne
          obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
            obtain ⟨g', c', w'⟩ := s'
            have hI' := hI.step hstep hs'
            simp only [mem_support_prodPMF] at hs'
            obtain ⟨hh1, hh2⟩ := hs'
            rw [PMF.mem_support_map_iff] at hh1; rw [PMF.mem_support_pure_iff] at hh2
            obtain ⟨gr', hgr', heq⟩ := hh1
            have hc : c' = c := congrArg Prod.fst hh2
            have hw : w' = w := congrArg Prod.snd hh2
            exact ⟨hI', by rw [← heq, hc, hw]; exact hAbs.step_gbcaTau hI r hstepG hgr' hUnan⟩)
          exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- rows 2/8: core τ (DECIDED delivery/echo/byz)
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨h1, h2, h3⟩ := hs'
          exact ⟨hI', by rw [h1, h3]; exact hAbs.step_coreTau hstepC h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row 6: WCC flip — always a constant-coupled stutter (v2.2: `coin_bot`, `Abs` never
        -- reads `w`, so every outcome of the coin lands on the same abstract twin `a`)
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff] at hs'
          obtain ⟨h1, h2, _⟩ := hs'
          exact ⟨hI', by rw [h1, h2]; exact hAbs.w_irrelevant⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨⟨gr', hgr', heq⟩, h2, h3⟩ := hs'
          exact ⟨hI', by rw [← heq, h3]; exact hAbs.step_callG r id b hstepG hstepC hgr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retG handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨⟨gr', hgr', heq⟩, h2, h3⟩ := hs'
          exact ⟨hI', by
            rw [← heq, h3]; exact hAbs.step_retG hI r id out bound hstepG hstepC hgr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: callW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨h1, h2, ⟨wr', hwr', heq⟩⟩ := hs'
          exact ⟨hI', by rw [h1, ← heq]; exact hAbs.step_callW r id hstepW hstepC hwr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
      · -- row: retW handshake
        obtain ⟨ω, hRel, hWeak⟩ := stutter_step _ a (fun s' hs' => by
          obtain ⟨g', c', w'⟩ := s'
          have hI' := hI.step hstep hs'
          simp only [mem_support_prodPMF, PMF.mem_support_pure_iff,
            PMF.mem_support_map_iff] at hs'
          obtain ⟨h1, h2, ⟨wr', hwr', heq⟩⟩ := hs'
          exact ⟨hI', by rw [h1, ← heq]; exact hAbs.step_retW r id b hstepW hstepC hwr' h2⟩)
        exact ⟨ω, hRel, Or.inl ⟨rfl, hWeak⟩⟩
    | callABA id b =>
      rw [hybrid_step_callABA] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      have hdisj := (coreStep_callABA_iff P c id b μc).mp hstepC
      rcases hdisj with ⟨hin, rfl⟩ | rfl
      · -- genuine fresh input
        set c' := c.setProc id { c.procs id with
          input := some b, est := some b, round := 0, phase := .toCallG } with hc'def
        have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
        have hIA' : Inv P g c' w := Inv.step_callABA hI id b hstepC hc'mem
        by_cases hbindNone : a.bind = none
        · by_cases hdis : ∃ id', id' ∉ c.F ∧ (c.procs id').input = some (!b)
          · -- dissent (design v2.2): an honest process holds the opposite input `!b`.
            obtain ⟨idd, hiddF, hiddin⟩ := hdis
            have hidd_ne : idd ≠ id := by
              rintro rfl; rw [hin] at hiddin; exact absurd hiddin (by simp)
            have hcallnone : a.call id = none := by rw [hAbs.call_pre hbindNone id, hin]
            by_cases hidF : id ∈ c.F
            · -- fresh input is Byzantine: honest inputs stay unanimous, so answer plain rule 1.
              set a' : SpecState P.n := { a with call := Function.update a.call id (some b) }
                with ha'def
              have ha'bind : a'.bind = none := by rw [ha'def]; exact hbindNone
              have hAbs' : Abs P g c' w a' := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · show a.F = c'.F
                  rw [hc'def, CoreState.setProc_F]; exact hAbs.F_eq
                · intro id'
                  rw [hc'def]
                  by_cases h : id' = id
                  · rw [h, CoreState.setProc_procs_self]; exact hAbs.ret_eq id
                  · rw [CoreState.setProc_procs_ne _ _ _ h]; exact hAbs.ret_eq id'
                · intro _ id'
                  show (Function.update a.call id (some b)) id' = (c'.procs id').input
                  by_cases h : id' = id
                  · rw [h, Function.update_self, hc'def, CoreState.setProc_procs_self]
                  · rw [Function.update_of_ne h, hc'def, CoreState.setProc_procs_ne _ _ _ h]
                    exact hAbs.call_pre hbindNone id'
                · intro h; exact absurd ha'bind h
                · rw [ha'def]; exact hAbs.coin_bot
                · intro v hv; exact hAbs.val_cert v (by rw [ha'def] at hv; exact hv)
                · intro _
                  obtain ⟨hNoC, hPool⟩ := hAbs.bind_ready hbindNone
                  refine ⟨hNoC, fun r v hbv => ?_⟩
                  obtain ⟨hp1, hp2⟩ := hPool r v hbv
                  refine ⟨fun id1 hf1 b1 hin1 => ?_, ?_⟩
                  · have hne1 : id1 ≠ id := fun h => hf1 (h ▸ hidF)
                    rw [hc'def, CoreState.setProc_procs_ne _ _ _ hne1] at hin1
                    exact hp1 id1 hf1 b1 hin1
                  · refine le_trans hp2 (Finset.card_le_card ?_)
                    intro i hi
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
                    by_cases h : i = id
                    · rw [h, hin] at hi; exact absurd hi (by simp)
                    · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]; exact hi
              rw [prodPMF_pure_pure_pure]
              obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a' ⟨hIA', hAbs'⟩
              refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
              rw [hbid]
              exact weakStep_strong (SpecStep.callSet a id b hcallnone hbindNone)
            · -- fresh input is honest: the first genuine honest dissent.  Split on whether any
              -- round is already bound (v2.2 amendment).
              by_cases hb : ∃ rr, (g rr).bind ≠ none
              case neg =>
                -- no round bound anywhere: `bind_ready`'s pool conjunct is vacuous, so plain
                -- rule-1 bank + stutter (mirrors the non-dissent unbound branch).
                push_neg at hb
                set a' : SpecState P.n := { a with call := Function.update a.call id (some b) }
                  with ha'def
                have hcallnone : a.call id = none := by rw [hAbs.call_pre hbindNone id, hin]
                have ha'bind : a'.bind = none := by rw [ha'def]; exact hbindNone
                have hAbs' : Abs P g c' w a' := by
                  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                  · show a.F = c'.F
                    rw [hc'def, CoreState.setProc_F]; exact hAbs.F_eq
                  · intro id'
                    rw [hc'def]
                    by_cases h : id' = id
                    · rw [h, CoreState.setProc_procs_self]; exact hAbs.ret_eq id
                    · rw [CoreState.setProc_procs_ne _ _ _ h]; exact hAbs.ret_eq id'
                  · intro _ id'
                    show (Function.update a.call id (some b)) id' = (c'.procs id').input
                    by_cases h : id' = id
                    · rw [h, Function.update_self, hc'def, CoreState.setProc_procs_self]
                    · rw [Function.update_of_ne h, hc'def, CoreState.setProc_procs_ne _ _ _ h]
                      exact hAbs.call_pre hbindNone id'
                  · intro h; exact absurd ha'bind h
                  · rw [ha'def]; exact hAbs.coin_bot
                  · intro v hv; exact hAbs.val_cert v (by rw [ha'def] at hv; exact hv)
                  · intro _
                    exact ⟨(hAbs.bind_ready hbindNone).1,
                      fun r v hbv => absurd ((hb r).symm.trans hbv) (by simp)⟩
                rw [prodPMF_pure_pure_pure]
                obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a' ⟨hIA', hAbs'⟩
                refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
                rw [hbid]
                exact weakStep_strong (SpecStep.callSet a id b hcallnone hbindNone)
              obtain ⟨rr, hrr⟩ := hb
              -- a round is bound: bank (rule 1) then bind (rule 4) in the τ-tail.
              set a1 : SpecState P.n := { a with call := Function.update a.call id (some b) }
                with ha1def
              have ha1call : a1.call = Function.update a.call id (some b) := rfl
              have ha1F : a1.F = c.F := by rw [ha1def]; exact hAbs.F_eq
              have ha1_id : a1.call id = some b := by rw [ha1call, Function.update_self]
              have ha1_idd : a1.call idd = some (!b) := by
                rw [ha1call, Function.update_of_ne hidd_ne, hAbs.call_pre hbindNone idd]
                exact hiddin
              -- The rule-4 quorum guard for the banked state transfers from the bound round `rr`
              -- via `abstract_quorum_of_call` (`Inv.bound_quorum` + `input_called` + `call_pre`).
              have hq1 : a1.quorum P :=
                abstract_quorum_of_call (aF := a1.F) (aCall := a1.call) hI (by rw [ha1F])
                  (fun id0 _ hin0 => by
                    by_cases h : id0 = id
                    · rw [h, ha1_id]; simp
                    · rw [ha1call, Function.update_of_ne h, hAbs.call_pre hbindNone id0]
                      exact hin0)
                  (r := rr) hrr
              have h1 : ∃ i, i ∉ a1.F ∧ a1.call i = some true := by
                by_cases hbb : b = true
                · exact ⟨id, by rw [ha1F]; exact hidF, by simp [ha1_id, hbb]⟩
                · have hbf : b = false := by cases b <;> simp_all
                  exact ⟨idd, by rw [ha1F]; exact hiddF, by simp [ha1_idd, hbf]⟩
              have h0 : ∃ i, i ∉ a1.F ∧ a1.call i = some false := by
                by_cases hbb : b = true
                · exact ⟨idd, by rw [ha1F]; exact hiddF, by simp [ha1_idd, hbb]⟩
                · have hbf : b = false := by cases b <;> simp_all
                  exact ⟨id, by rw [ha1F]; exact hidF, by simp [ha1_id, hbf]⟩
              set a2 : SpecState P.n :=
                { a1 with call := fun _ => none, bind := some b, coin := .bot } with ha2def
              have hburst : weakTau (spec P) (PMF.pure a1) (PMF.pure a2) :=
                weakTau_of_step rfl (SpecStep.mixed a1 b hq1 h1 h0)
              have hAbs2 : Abs P g c' w a2 := by
                refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
                · show a2.F = c'.F
                  rw [ha2def]; show a1.F = c'.F
                  rw [ha1F, hc'def, CoreState.setProc_F]
                · intro id'
                  rw [hc'def]
                  by_cases h : id' = id
                  · rw [h, CoreState.setProc_procs_self]; exact hAbs.ret_eq id
                  · rw [CoreState.setProc_procs_ne _ _ _ h]; exact hAbs.ret_eq id'
                · intro h; exact absurd h (by rw [ha2def]; simp)
                · intro _ id'; rw [ha2def]
                · rw [ha2def]
                · intro v hv; exact hAbs.val_cert v hv
                · intro h; exact absurd h (by rw [ha2def]; simp)
              rw [prodPMF_pure_pure_pure]
              obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a2 ⟨hIA', hAbs2⟩
              refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
              rw [hbid]
              exact weakStep_of_step_then_burst (SpecStep.callSet a id b hcallnone hbindNone) hburst
          · push_neg at hdis
            set a' : SpecState P.n := { a with call := Function.update a.call id (some b) }
              with ha'def
            have hcallnone : a.call id = none := by rw [hAbs.call_pre hbindNone id, hin]
            have ha'bind : a'.bind = none := by rw [ha'def]; exact hbindNone
            have hallb : ∀ id', id' ∉ c.F → ∀ b', (c'.procs id').input = some b' → b' = b := by
              intro id' hid'F b' hb'
              by_cases h : id' = id
              · rw [h, hc'def, CoreState.setProc_procs_self] at hb'
                exact Option.some_inj.mp hb'.symm
              · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h] at hb'
                by_contra hne
                exact hdis id' hid'F (by cases b' <;> cases b <;> simp_all)
            have hAbs' : Abs P g c' w a' := by
              refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
              · show a.F = c'.F
                rw [hc'def, CoreState.setProc_F]; exact hAbs.F_eq
              · intro id'
                rw [hc'def]
                by_cases h : id' = id
                · rw [h, CoreState.setProc_procs_self]; exact hAbs.ret_eq id
                · rw [CoreState.setProc_procs_ne _ _ _ h]; exact hAbs.ret_eq id'
              · intro _ id'
                show (Function.update a.call id (some b)) id' = (c'.procs id').input
                by_cases h : id' = id
                · rw [h, Function.update_self, hc'def, CoreState.setProc_procs_self]
                · rw [Function.update_of_ne h, hc'def, CoreState.setProc_procs_ne _ _ _ h]
                  exact hAbs.call_pre hbindNone id'
              · intro h; exact absurd ha'bind h
              · rw [ha'def]; exact hAbs.coin_bot
              · intro v hv
                exact hAbs.val_cert v (by rw [ha'def] at hv; exact hv)
              · intro _
                obtain ⟨hNoC, hPool⟩ := hAbs.bind_ready hbindNone
                refine ⟨hNoC, fun r v hbv => ?_⟩
                obtain ⟨hp1, hp2⟩ := hPool r v hbv
                have hex : ∃ id'', id'' ∉ c.F ∧ (c.procs id'').input = some v := by
                  by_contra hcon; push_neg at hcon
                  have hsub : (Finset.univ.filter (fun id2 => (c.procs id2).input = some v)) ⊆
                      c.F := by
                    intro id2 hid2
                    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hid2
                    by_contra hnf; exact hcon id2 hnf hid2
                  have hcard := Finset.card_le_card hsub
                  have hfc := hI.F_card
                  omega
                obtain ⟨id'', hid''F, hid''in⟩ := hex
                have hidne : id'' ≠ id := by
                  rintro rfl; rw [hin] at hid''in; exact absurd hid''in (by simp)
                have hveqb : v = b := hallb id'' hid''F v (by
                  rw [hc'def, CoreState.setProc_procs_ne _ _ _ hidne]; exact hid''in)
                refine ⟨fun id' hf' b' hb' => (hallb id' hf' b' hb').trans hveqb.symm, ?_⟩
                rw [hveqb] at hp2 ⊢
                have hsub2 : (Finset.univ.filter (fun id2 => (c.procs id2).input = some b)) ⊆
                    (Finset.univ.filter (fun id2 => (c'.procs id2).input = some b)) := by
                  intro id2 hid2
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hid2 ⊢
                  by_cases h : id2 = id
                  · rw [h, hc'def, CoreState.setProc_procs_self]
                  · rw [hc'def, CoreState.setProc_procs_ne _ _ _ h]; exact hid2
                exact le_trans hp2 (Finset.card_le_card hsub2)
            rw [prodPMF_pure_pure_pure]
            obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a' ⟨hIA', hAbs'⟩
            refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
            rw [hbid]
            exact weakStep_strong (SpecStep.callSet a id b hcallnone hbindNone)
        · -- `a` already bound: answer rule 2 (loop); `c'`'s new input is `call_pre`-irrelevant
          have hAbs' : Abs P g c' w a :=
            ⟨by rw [hc'def, CoreState.setProc_F]; exact hAbs.F_eq,
              fun id' => by
                rw [hc'def]; by_cases h : id' = id
                · rw [h, CoreState.setProc_procs_self]; exact hAbs.ret_eq id
                · rw [CoreState.setProc_procs_ne _ _ _ h]; exact hAbs.ret_eq id',
              fun h => absurd h hbindNone, hAbs.call_post,
              hAbs.coin_bot, hAbs.val_cert, fun h => absurd h hbindNone⟩
          rw [prodPMF_pure_pure_pure]
          obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a ⟨hIA', hAbs'⟩
          refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
          rw [hbid]
          exact weakStep_strong (SpecStep.callLoop a id b)
      · -- concrete self-loop: answer rule 2 (loop) always
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c, w) a ⟨hI, hAbs⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_strong (SpecStep.callLoop a id b)
    | retABA id b =>
      rw [hybrid_step_retABA] at hstep
      obtain ⟨μc, hstepC, rfl⟩ := hstep
      rw [coreStep_retABA_iff] at hstepC
      obtain ⟨hcnt, hs, hret, rfl⟩ := hstepC
      set c' := c.setProc id { c.procs id with returned := true } with hc'def
      have hc'mem : c' ∈ (PMF.pure c').support := by rw [PMF.mem_support_pure_iff]
      have hIA' : Inv P g c' w := by
        have := Inv.step_retABA hI id b (by
          rw [coreStep_retABA_iff]; exact ⟨hcnt, hs, hret, rfl⟩) hc'mem
        exact this
      -- Honest DECIDED-sender pigeonhole: `n − f` deliveries of `b` to `id`, only `f` corrupted.
      have hex : ∃ j, j ∉ c.F ∧ c.decidedRecv id j = some b := by
        by_contra hcon; push_neg at hcon
        have hsub : (Finset.univ.filter (fun j => c.decidedRecv id j = some b)) ⊆ c.F := by
          intro j hj
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
          by_contra hnf; exact hcon j hnf hj
        have hcard := Finset.card_le_card hsub
        have hfc := hI.F_card
        have hf3 := P.hf
        unfold CoreState.decidedCount at hcnt
        omega
      obtain ⟨j, hjF, hjrecv⟩ := hex
      have hjsent : c.decidedSent j = some b := hI.recv_sound id j b hjF hjrecv
      obtain ⟨rA, hrA_grade, hrA_bind⟩ := hI.decided_src j b hjF hjsent
      have hretfalse : a.ret id = false := by rw [hAbs.ret_eq id]; exact hret
      by_cases hbindNone : a.bind = none
      · -- `a` unbound: bind `b` via rule 3 (unanim) — `b` is the unanimous honest input
        -- (`bind_ready` at the A-locked DECIDED source `rA`, so no honest input is `!b`),
        -- quorum via `abstract_quorum_of_call` on the bound round `rA`; then rule 8.
        have hq : a.quorum P := abstract_quorum_of_call (aF := a.F) (aCall := a.call) hI
          hAbs.F_eq (fun id _ hin => by rw [hAbs.call_pre hbindNone id]; exact hin)
          (r := rA) (by rw [hrA_bind]; simp)
        obtain ⟨_, hPool⟩ := hAbs.bind_ready hbindNone
        obtain ⟨hunan, _⟩ := hPool rA b hrA_bind
        have hb : ∀ id, id ∉ a.F → a.call id ≠ some (!b) := by
          intro id hidF hcontra
          rw [hAbs.call_pre hbindNone id] at hcontra
          exact absurd (hunan id (hAbs.F_eq ▸ hidF) (!b) hcontra) (by cases b <;> simp)
        have hreb := rebind_unanim (a := a) (b := !b) hq hb
        rw [Bool.not_not] at hreb
        set a0 : SpecState P.n :=
          { a with call := fun _ => none, bind := some b, val := some b, coin := .bot }
          with ha0def
        have hval'0 : a0.val = some b := rfl
        have hbind'0 : a0.bind = some b := rfl
        have hcall'0 : a0.call = (fun _ => none) := rfl
        have hcoin'0 : a0.coin = .bot := rfl
        have hF'0 : a0.F = a.F := rfl
        have hret'0 : a0.ret = a.ret := rfl
        have hretid : a0.ret id = false := by rw [hret'0]; exact hretfalse
        set a'' : SpecState P.n := { a0 with ret := Function.update a0.ret id true } with ha''def
        have ha''ret : ∀ id', a''.ret id' = Function.update a0.ret id true id' := fun _ => rfl
        have ha''bind : a''.bind = a0.bind := rfl
        have ha''val : a''.val = a0.val := rfl
        have ha''coin : a''.coin = a0.coin := rfl
        have ha''F : a''.F = a0.F := rfl
        have hAbs'' : Abs P g c' w a'' := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [ha''F, hF'0, hAbs.F_eq, hc'def, CoreState.setProc_F]
          · intro id'
            rw [ha''ret id', hc'def]
            by_cases h : id' = id
            · simp [h, CoreState.setProc_procs_self]
            · rw [Function.update_of_ne h, CoreState.setProc_procs_ne _ _ _ h]
              exact hAbs.ret_eq id'
          · intro h; exact absurd (ha''bind ▸ h : a0.bind = none) (by rw [hbind'0]; simp)
          · intro _ id'
            show a''.call id' = none
            have : a''.call = a0.call := rfl
            rw [this, hcall'0]
          · exact hcoin'0
          · intro v hv
            rw [ha''val, hval'0] at hv
            have hveqb : v = b := (Option.some_inj.mp hv).symm
            rw [hveqb]; exact ⟨rA, hrA_grade, hrA_bind⟩
          · intro h; exact absurd (ha''bind ▸ h : a0.bind = none) (by rw [hbind'0]; simp)
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a'' ⟨hIA', hAbs''⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_of_burst_then_step hreb (SpecStep.ret a0 id b hval'0 hretid)
      · -- `a` already bound: D3-compat via `commit_up`, then `val_force'` + rule 8.
        have hvbex : ∃ vb0, a.bind = some vb0 :=
          match hb : a.bind with
          | none => absurd hb hbindNone
          | some vb0 => ⟨vb0, rfl⟩
        obtain ⟨vb, hvb⟩ := hvbex
        have hD3 : ∀ x, a.val = some x → x = b := by
          intro x hx
          obtain ⟨rx, hrx_grade, hrx_bind⟩ := hAbs.val_cert x hx
          rcases le_total rA rx with hle | hle
          · obtain ⟨hbcase, _⟩ := hI.commit_up rA b (by rw [hrA_grade]; simp) hrA_bind rx hle
            rcases hbcase with hn | hs
            · rw [hn] at hrx_bind; simp at hrx_bind
            · rw [hrx_bind] at hs; exact Option.some_inj.mp hs
          · obtain ⟨hbcase, _⟩ := hI.commit_up rx x (by rw [hrx_grade]; simp) hrx_bind rA hle
            rcases hbcase with hn | hs
            · rw [hn] at hrA_bind; simp at hrA_bind
            · rw [hrA_bind] at hs; exact (Option.some_inj.mp hs).symm
        have hvalcase : a.val = none ∨ a.val = some b := by
          rcases hav : a.val with _ | x
          · exact Or.inl rfl
          · exact Or.inr (by rw [hD3 x hav])
        obtain ⟨a', hburst, hval', hbind', hcall', hret', hF', hcoin'⟩ :=
          val_force' hvb (hAbs.call_post hbindNone) hAbs.coin_bot hvalcase
        have hretid : a'.ret id = false := by rw [hret']; exact hretfalse
        set a'' : SpecState P.n := { a' with ret := Function.update a'.ret id true } with ha''def
        have ha''ret : ∀ id', a''.ret id' = Function.update a'.ret id true id' := fun _ => rfl
        have ha''bind : a''.bind = a'.bind := rfl
        have ha''val : a''.val = a'.val := rfl
        have ha''coin : a''.coin = a'.coin := rfl
        have ha''F : a''.F = a'.F := rfl
        have hAbs'' : Abs P g c' w a'' := by
          refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · rw [ha''F, hF', hAbs.F_eq, hc'def, CoreState.setProc_F]
          · intro id'
            rw [ha''ret id', hc'def]
            by_cases h : id' = id
            · simp [h, CoreState.setProc_procs_self]
            · rw [Function.update_of_ne h, CoreState.setProc_procs_ne _ _ _ h,
                congrFun hret' id']
              exact hAbs.ret_eq id'
          · intro h; exact absurd (ha''bind ▸ h : a'.bind = none) (by rw [hbind']; simp)
          · intro _ id'
            show a''.call id' = none
            have : a''.call = a'.call := rfl
            rw [this, hcall']
          · rw [ha''coin]; exact hcoin'
          · intro v hv
            rw [ha''val, hval'] at hv
            have hveqb : v = b := (Option.some_inj.mp hv).symm
            rw [hveqb]; exact ⟨rA, hrA_grade, hrA_bind⟩
          · intro h; exact absurd (ha''bind ▸ h : a'.bind = none) (by rw [hbind']; simp)
        rw [prodPMF_pure_pure_pure]
        obtain ⟨ω, hRel, hbid⟩ := dirac_step (g, c', w) a'' ⟨hIA', hAbs''⟩
        refine ⟨ω, hRel, Or.inr ⟨by simp, ?_⟩⟩
        rw [hbid]
        exact weakStep_of_burst_then_step hburst (SpecStep.ret a' id b hval' hretid)
    | callG r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retG r id out bound => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | callW r id => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | retW r id b => exact (hidden_label_impossible (by simp) (by simp) hstep).elim
    | fail id =>
      rw [hybrid_step_fail] at hstep
      subst hstep
      have hEq : prodPMF (PMF.pure (fun r => (g r).corrupt P id))
          (prodPMF (PMF.pure (c.corrupt P id)) (PMF.pure (fun r => (w r).corrupt P id))) =
          PMF.pure (fun r => (g r).corrupt P id, (c.corrupt P id, fun r => (w r).corrupt P id)) := by
        simp [prodPMF, PMF.pure_bind]
      rw [hEq]
      have hFsub := CoreState.corrupt_F_subset c id
      have hAbs' : Abs P (fun r => (g r).corrupt P id) (c.corrupt P id)
          (fun r => (w r).corrupt P id) (a.corrupt P id) := by
        refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · show (a.corrupt P id).F = (c.corrupt P id).F
          unfold SpecState.corrupt CoreState.corrupt
          rw [hAbs.F_eq]; split_ifs <;> simp [hAbs.F_eq]
        · intro id'
          rw [SpecState.corrupt_ret, CoreState.corrupt_procs]; exact hAbs.ret_eq id'
        · intro hbind id'
          rw [SpecState.corrupt_call, CoreState.corrupt_procs]
          rw [SpecState.corrupt_bind] at hbind
          exact hAbs.call_pre hbind id'
        · intro hbind id'
          rw [SpecState.corrupt_call]
          rw [SpecState.corrupt_bind] at hbind
          exact hAbs.call_post hbind id'
        · rw [SpecState.corrupt_coin]; exact hAbs.coin_bot
        · intro v hv
          rw [SpecState.corrupt_val] at hv
          obtain ⟨r0, hg0, hb0⟩ := hAbs.val_cert v hv
          exact ⟨r0, by rw [GBCA.corrupt_grade]; exact hg0, by rw [GBCA.corrupt_bind]; exact hb0⟩
        · intro hbind
          rw [SpecState.corrupt_bind] at hbind
          obtain ⟨hNoC, hPool⟩ := hAbs.bind_ready hbind
          refine ⟨fun r => by rw [GBCA.corrupt_grade]; exact hNoC r, fun r v hbv => ?_⟩
          · rw [GBCA.corrupt_bind] at hbv
            obtain ⟨hp1, hp2⟩ := hPool r v hbv
            refine ⟨fun id1 hf1 b1 hin1 => ?_, ?_⟩
            · rw [CoreState.corrupt_procs] at hin1
              exact hp1 id1 (fun h => hf1 (hFsub h)) b1 hin1
            · rwa [CoreState.corrupt_procs]
      have hIA' : Inv P (fun r => (g r).corrupt P id) (c.corrupt P id)
          (fun r => (w r).corrupt P id) := hI.step_fail id
      refine ⟨PMF.pure (PMF.pure (a.corrupt P id)), ⟨PMF.pure
        ((fun r => (g r).corrupt P id, (c.corrupt P id, fun r => (w r).corrupt P id)),
          PMF.pure (a.corrupt P id)), ?_, ?_, ?_⟩, Or.inr ⟨by simp, ?_⟩⟩
      · rw [PMF.pure_map]
      · rw [PMF.pure_map]
      · intro p hp
        rw [PMF.mem_support_pure_iff] at hp
        subst hp
        exact ⟨a.corrupt P id, rfl, hIA', hAbs'⟩
      · rw [PMF.pure_bind]
        exact weakStep_strong (SpecStep.fail a id)

end ABA
end PLTS
