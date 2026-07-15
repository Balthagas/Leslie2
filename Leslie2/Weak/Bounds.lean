/-
Copyright (c) 2026 Gaspard Reghem. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaspard Reghem
-/

import Leslie2.Weak.BoundsHalt

/-!
# Halt-below identity `probOf_eq_haltBelow`

Under almost-sure halting, the probability of a terminating execution `e` equals the total halting
mass over all finite continuations of `e` (`haltBelow`). A limit-free flow-conservation argument:
the "escape" mass `esc = probOf - haltBelow` is conserved level by level and every level sum is
`0`. The underlying halt-mass bounds live in `Weak/BoundsHalt.lean`.
-/

open Stream'

namespace PLTS

variable {α β State State_C State_A Label : Type} [Silent Label]

/-! ### Halt-below identity `probOf_eq_haltBelow`

Under almost-sure halting (`hAS`), the probability of a terminating execution `e`
equals the total halting mass over all finite continuations of `e` (`haltBelow`).
This is a *limit-free* flow-conservation argument: the "escape" mass
`esc = probOf − haltBelow` is conserved level by level, and the level sums are all
`0` (the level-`0` sum is `∑ init − ∑ (all halt mass) = 1 − 1 = 0`). -/

/-- Generic ENNReal `tsum` subtraction over an arbitrary index type (the Mathlib
`ENNReal.tsum_sub` is stated only for `ℕ`). -/
private theorem tsum_sub_gen {ι : Type*} {f g : ι → ENNReal}
    (h₁ : (∑' i, g i) ≠ ⊤) (h₂ : g ≤ f) :
    (∑' i, (f i - g i)) = (∑' i, f i) - ∑' i, g i := by
  have key : (∑' i, (f i - g i)) + ∑' i, g i = ∑' i, f i := by
    rw [← ENNReal.tsum_add]
    exact tsum_congr (fun i => tsub_add_cancel_of_le (h₂ i))
  rw [← key, ENNReal.add_sub_cancel_right h₁]

/-- The pure algebraic core of flow conservation: from `P = c + A`, `HB = c + B`,
`E = A − B` with `B ≤ A` and `HB ≠ ⊤`, deduce `P − HB = E`. -/
private theorem esc_flow_of {P HB c A B E : ENNReal}
    (hP : P = c + A) (hHB : HB = c + B) (hE : E = A - B)
    (hBA : B ≤ A) (hHBfin : HB ≠ ⊤) :
    P - HB = E := by
  have hsum : E + HB = P := by
    rw [hE, hP, hHB, add_comm c B, ← add_assoc, tsub_add_cancel_of_le hBA, add_comm A c]
  rw [← hsum, ENNReal.add_sub_cancel_right hHBfin]

/-- The canonical bijection `Option (γ × List γ) ≃ List γ` (`none ↦ []`,
`some (a, t) ↦ a :: t`), used to split a `tsum` over lists into the empty list
plus the `cons`-headed lists. -/
private def listOptionEquiv (γ : Type) : Option (γ × List γ) ≃ List γ where
  toFun o := o.elim [] (fun p => p.1 :: p.2)
  invFun l := l.casesOn none (fun a t => some (a, t))
  left_inv o := by cases o with | none => rfl | some p => rfl
  right_inv l := by cases l with | nil => rfl | cons a t => rfl

/-- Split a `tsum` over lists into the empty-list term plus a `tsum` over
`cons`-headed lists. -/
private theorem listTsum_cons_split {γ : Type} (f : List γ → ENNReal) :
    (∑' t : List γ, f t) = f [] + ∑' q : γ × List γ, f (q.1 :: q.2) := by
  rw [← Equiv.tsum_eq (listOptionEquiv γ) f, ENNReal.tsum_option']
  rfl

/-- Termination of `sq ++ ofList t` for any finite `sq` and list `t`. -/
theorem append_ofList_terminates {State Label : Type} {sq : Seq (Label × State)}
    (h : sq.Terminates) (t : List (Label × State)) :
    (sq.append (Seq.ofList t)).Terminates :=
  ⟨_, Stream'.Seq.terminatedAt_append_find h (Nat.find_spec (Stream'.Seq.terminates_ofList t))⟩

open Classical in
/-- The total halt-mass over all finite continuations `t` of a terminating
execution `e` (with `t = []` giving `e` itself). -/
noncomputable def ProbabilisticExecution.haltBelow {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (e : AlterSeq State Label) (h : e.trans.Terminates) : ENNReal :=
  ∑' t : List (Label × State),
    (pe.probOf ⟨e.init, e.trans.append (Seq.ofList t)⟩ (append_ofList_terminates h t)
      * pe.scheduler.next ⟨e.init, e.trans.append (Seq.ofList t)⟩ none)

/-- `escP pe s L = probOf ⟨s, ofList L⟩`: the probability of the canonical
terminating execution with initial state `s` and transition list `L`. -/
private noncomputable def escP {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) : ENNReal :=
  pe.probOf ⟨s, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)

/-- `haltNode pe s L = escP pe s L * next ⟨s, ofList L⟩ none`: the halt mass at
the single node `⟨s, ofList L⟩`. -/
private noncomputable def haltNode {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) : ENNReal :=
  escP pe s L * pe.scheduler.next ⟨s, Seq.ofList L⟩ none

/-- `escHB pe s L = ∑' t, haltNode pe s (L ++ t)`: the halt mass below the node
`⟨s, ofList L⟩` (the `ofList`-form of `haltBelow`). -/
private noncomputable def escHB {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) : ENNReal :=
  ∑' t : List (Label × State), haltNode pe s (L ++ t)

/-- `esc pe s L = escP pe s L − escHB pe s L`: the escape mass at node
`⟨s, ofList L⟩` (ENNReal truncated subtraction). -/
private noncomputable def esc {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) : ENNReal :=
  escP pe s L - escHB pe s L

/-- `escP ≤ 1`: probabilities of terminating executions are bounded by `1`. -/
private theorem escP_le_one {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escP pe s L ≤ 1 := by
  unfold escP
  exact (pe.probOf_le_init ⟨s, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L)).trans
    (PMF.coe_le_one _ _)

private theorem escP_ne_top {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escP pe s L ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (escP_le_one pe s L)

/-- `escHB` factors as `escP` times the relative halt-mass path sum. -/
private theorem escHB_eq_mul {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escHB pe s L = escP pe s L
      * ∑' t : List (Label × State),
          (pe.pathWeight ⟨s, Seq.ofList L⟩ t
            * pe.scheduler.next ⟨s, (Seq.ofList L).append (Seq.ofList t)⟩ none) := by
  unfold escHB
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun t => ?_
  unfold haltNode escP
  have happ : (Seq.ofList (L ++ t) : Seq (Label × State))
      = (Seq.ofList L).append (Seq.ofList t) := Stream'.Seq.ofList_append L t
  rw [pe.probOf_congr ⟨s, Seq.ofList (L ++ t)⟩ ⟨s, (Seq.ofList L).append (Seq.ofList t)⟩
      (by rw [happ]) (Stream'.Seq.terminates_ofList _)
      (append_ofList_terminates (Stream'.Seq.terminates_ofList L) t),
    pe.probOf_append_ofList ⟨s, Seq.ofList L⟩ (Stream'.Seq.terminates_ofList L) t
      (append_ofList_terminates (Stream'.Seq.terminates_ofList L) t),
    show pe.scheduler.next ⟨s, Seq.ofList (L ++ t)⟩ none
        = pe.scheduler.next ⟨s, (Seq.ofList L).append (Seq.ofList t)⟩ none from by rw [happ]]
  ring

/-- `escHB ≤ escP`: the halt mass below a node cannot exceed its probability. -/
private theorem escHB_le_escP {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escHB pe s L ≤ escP pe s L := by
  rw [escHB_eq_mul]
  calc escP pe s L
        * ∑' t : List (Label × State),
            (pe.pathWeight ⟨s, Seq.ofList L⟩ t
              * pe.scheduler.next ⟨s, (Seq.ofList L).append (Seq.ofList t)⟩ none)
      ≤ escP pe s L * 1 := by
        gcongr
        exact pe.pathWeight_halt_tsum_le_one ⟨s, Seq.ofList L⟩
    _ = escP pe s L := mul_one _

private theorem escHB_ne_top {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escHB pe s L ≠ ⊤ :=
  ne_top_of_le_ne_top (escP_ne_top pe s L) (escHB_le_escP pe s L)

/-- The one-step conservation of mass: halting now plus all one-step kernels
sums to `1`. -/
private theorem kernel_halt_sum {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (e : AlterSeq State Label) :
    pe.scheduler.next e none + ∑' p : Label × State, pe.kernel e p = 1 := by
  have h1 : (∑' p : Label × State, pe.kernel e p)
      = ∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ) := by
    calc (∑' p : Label × State, pe.kernel e p)
        = ∑' (l : Label) (s' : State), pe.kernel e (l, s') := by rw [ENNReal.tsum_prod']
      _ = ∑' (l : Label) (s' : State) (μ : PMF State),
            pe.scheduler.next e (some (l, μ)) * μ s' := by rfl
      _ = ∑' (l : Label) (μ : PMF State) (s' : State),
            pe.scheduler.next e (some (l, μ)) * μ s' := by
          refine tsum_congr fun l => ?_; exact ENNReal.tsum_comm
      _ = ∑' (l : Label) (μ : PMF State), pe.scheduler.next e (some (l, μ)) := by
          refine tsum_congr fun l => tsum_congr fun μ => ?_
          rw [ENNReal.tsum_mul_left, μ.tsum_coe, mul_one]
      _ = ∑' lμ : Label × PMF State, pe.scheduler.next e (some lμ) := by rw [ENNReal.tsum_prod']
  rw [h1, ← ENNReal.tsum_option' (fun opt => pe.scheduler.next e opt)]
  exact (pe.scheduler.next e).tsum_coe

/-- Appending one transition `x` multiplies `escP` by the one-step kernel. -/
private theorem escP_concat {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State))
    (x : Label × State) :
    escP pe s (L ++ [x]) = escP pe s L * pe.kernel ⟨s, Seq.ofList L⟩ x := by
  unfold escP
  have happ : (Seq.ofList (L ++ [x]) : Seq (Label × State))
      = (Seq.ofList L).append (Seq.cons x Seq.nil) := by
    rw [Stream'.Seq.ofList_append, Stream'.Seq.ofList_cons, Stream'.Seq.ofList_nil]
  rw [pe.probOf_congr ⟨s, Seq.ofList (L ++ [x])⟩ ⟨s, (Seq.ofList L).append (Seq.cons x Seq.nil)⟩
      (by rw [happ]) (Stream'.Seq.terminates_ofList _)
      (by rw [← happ]; exact Stream'.Seq.terminates_ofList _),
    pe.probOf_append_singleton s (Seq.ofList L) (Stream'.Seq.terminates_ofList L) x
      (by rw [← happ]; exact Stream'.Seq.terminates_ofList _)]

/-- One-step front-peel of `escP`: halting now plus escaping via each one-step
successor. -/
private theorem escP_split {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escP pe s L = haltNode pe s L + ∑' x : Label × State, escP pe s (L ++ [x]) := by
  rw [tsum_congr (fun x => escP_concat pe s L x), ENNReal.tsum_mul_left]
  unfold haltNode
  rw [← mul_add, kernel_halt_sum pe ⟨s, Seq.ofList L⟩, mul_one]

/-- One-step front-peel of `escHB`: halting now plus the halt mass below each
one-step successor. -/
private theorem escHB_split {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    escHB pe s L = haltNode pe s L + ∑' x : Label × State, escHB pe s (L ++ [x]) := by
  unfold escHB
  rw [listTsum_cons_split (fun t => haltNode pe s (L ++ t))]
  congr 1
  · rw [List.append_nil]
  · rw [ENNReal.tsum_prod']
    refine tsum_congr fun x => ?_
    refine tsum_congr fun t' => ?_
    congr 1
    rw [List.append_assoc]
    rfl

/-- **Flow conservation.** The escape mass at a node equals the total escape mass
of its one-step successors. -/
private theorem esc_flow {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (s : State) (L : List (Label × State)) :
    esc pe s L = ∑' x : Label × State, esc pe s (L ++ [x]) := by
  have hle : ∀ x, escHB pe s (L ++ [x]) ≤ escP pe s (L ++ [x]) :=
    fun x => escHB_le_escP pe s _
  have hAsum_le : (∑' x : Label × State, escP pe s (L ++ [x])) ≤ escP pe s L := by
    conv_rhs => rw [escP_split pe s L]
    exact le_add_self
  have bfin : (∑' x : Label × State, escHB pe s (L ++ [x])) ≠ ⊤ :=
    ne_top_of_le_ne_top (escP_ne_top pe s L) ((ENNReal.tsum_le_tsum hle).trans hAsum_le)
  have hE : (∑' x : Label × State, esc pe s (L ++ [x]))
      = (∑' x, escP pe s (L ++ [x])) - ∑' x, escHB pe s (L ++ [x]) := by
    unfold esc
    exact tsum_sub_gen bfin hle
  unfold esc
  exact esc_flow_of (escP_split pe s L) (escHB_split pe s L) hE
    (ENNReal.tsum_le_tsum hle) (escHB_ne_top pe s L)

/-- Append-at-end bijection: length-`(k+1)` lists ↔ (length-`k` list, last element). -/
private def snocEquiv {γ : Type} (k : ℕ) :
    {L₀ : List γ // L₀.length = k} × γ ≃ {L : List γ // L.length = k + 1} where
  toFun p := ⟨p.1.1 ++ [p.2], by rw [List.length_append, p.1.2]; rfl⟩
  invFun L := ⟨⟨L.1.dropLast, by rw [List.length_dropLast, L.2]; rfl⟩,
                L.1.getLast (List.ne_nil_of_length_pos (by rw [L.2]; exact Nat.succ_pos k))⟩
  left_inv := by
    rintro ⟨⟨L₀, hL₀⟩, x⟩
    refine Prod.ext (Subtype.ext ?_) ?_
    · exact List.dropLast_concat
    · exact List.getLast_concat
  right_inv := by
    rintro ⟨L, hL⟩
    exact Subtype.ext (List.dropLast_append_getLast _)

/-- Terminating executions ↔ (initial state, transition list). -/
private def termEquiv {State Label : Type} :
    State × List (Label × State) ≃ {g : AlterSeq State Label // g.trans.Terminates} where
  toFun p := ⟨⟨p.1, Seq.ofList p.2⟩, Stream'.Seq.terminates_ofList p.2⟩
  invFun g := (g.1.init, g.1.trans.toList g.2)
  left_inv := by
    rintro ⟨s, t⟩
    exact Prod.ext rfl (Stream'.Seq.toList_ofList t)
  right_inv := by
    rintro ⟨⟨i, tr⟩, hterm⟩
    refine Subtype.ext ?_
    change (⟨i, Seq.ofList (tr.toList hterm)⟩ : AlterSeq State Label) = ⟨i, tr⟩
    rw [Stream'.Seq.ofList_toList]

/-- The level-`k` escape sum: total escape mass over all nodes whose transition
list has length `k`. -/
private noncomputable def Lk {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (k : ℕ) : ENNReal :=
  ∑' s : State, ∑' L : {L : List (Label × State) // L.length = k}, esc pe s L.1

/-- **Level sums are constant** (one step of `k`): a consequence of flow
conservation and the snoc bijection. -/
private theorem Lk_succ {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys) (k : ℕ) :
    Lk pe (k + 1) = Lk pe k := by
  unfold Lk
  refine tsum_congr fun s => ?_
  rw [← Equiv.tsum_eq (snocEquiv k) (fun L => esc pe s L.1), ENNReal.tsum_prod']
  refine tsum_congr fun L₀ => ?_
  rw [esc_flow pe s L₀.1]
  refine tsum_congr fun x => ?_
  rfl

/-- **Base level sum is zero**: `∑ init − ∑ (total halt mass) = 1 − 1 = 0`. -/
private theorem Lk_zero {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys)
    (hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
              pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1) :
    Lk pe 0 = 0 := by
  unfold Lk
  have hinner : ∀ s, (∑' L : {L : List (Label × State) // L.length = 0}, esc pe s L.1)
      = esc pe s [] := by
    intro s
    exact tsum_eq_single (⟨[], rfl⟩ : {L : List (Label × State) // L.length = 0})
      (fun L' hne => absurd (Subtype.ext (List.length_eq_zero_iff.mp L'.2)) hne)
  rw [tsum_congr hinner]
  -- `∑' s, escP pe s [] = 1`
  have hP0 : (∑' s : State, escP pe s []) = 1 := by
    have hval : ∀ s, escP pe s [] = pe.initState s := by
      intro s
      unfold escP
      rw [pe.probOf_congr ⟨s, Seq.ofList []⟩ ⟨s, Seq.nil⟩ (by rw [Stream'.Seq.ofList_nil])
          (Stream'.Seq.terminates_ofList _) Stream'.Seq.terminates_nil,
        ProbabilisticExecution.probOf_nil, ProbabilisticExecution.init_eq_initState]
    rw [tsum_congr hval]; exact pe.initState.tsum_coe
  -- `∑' s, escHB pe s [] = 1` (reindex to `hAS`)
  have hHle : ∀ s, escHB pe s [] ≤ escP pe s [] := fun s => escHB_le_escP pe s []
  have hHB0 : (∑' s : State, escHB pe s []) = 1 := by
    have hterm : ∀ s, escHB pe s [] = ∑' t : List (Label × State), haltNode pe s t := by
      intro s; unfold escHB; exact tsum_congr fun t => by rw [List.nil_append]
    rw [tsum_congr hterm]
    calc (∑' s : State, ∑' t : List (Label × State), haltNode pe s t)
        = ∑' p : State × List (Label × State), haltNode pe p.1 p.2 := by rw [ENNReal.tsum_prod']
      _ = ∑' g : {g : AlterSeq State Label // g.trans.Terminates},
            pe.probOf g.1 g.2 * pe.scheduler.next g.1 none := by
          rw [← Equiv.tsum_eq termEquiv
            (fun g => pe.probOf g.1 g.2 * pe.scheduler.next g.1 none)]
          exact tsum_congr fun p => rfl
      _ = 1 := hAS
  have hsub : (∑' s : State, esc pe s [])
      = (∑' s : State, escP pe s []) - ∑' s : State, escHB pe s [] := by
    have hne : (∑' s : State, escHB pe s []) ≠ ⊤ := hHB0 ▸ ENNReal.one_ne_top
    calc (∑' s : State, esc pe s [])
        = ∑' s : State, (escP pe s [] - escHB pe s []) := by rfl
      _ = (∑' s : State, escP pe s []) - ∑' s : State, escHB pe s [] := tsum_sub_gen hne hHle
  rw [hsub, hP0, hHB0, tsub_self]

/-- All level sums are zero. -/
private theorem Lk_const {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys)
    (hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
              pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1) (k : ℕ) :
    Lk pe k = 0 := by
  induction k with
  | zero => exact Lk_zero pe hAS
  | succ n ih => rw [Lk_succ pe n, ih]

/-- **Escape is zero**: a single nonnegative summand of the (zero) level sum. -/
private theorem esc_zero {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys)
    (hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
              pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1)
    (s : State) (L : List (Label × State)) :
    esc pe s L = 0 := by
  have hbound : esc pe s L ≤ Lk pe L.length := by
    unfold Lk
    calc esc pe s L
        ≤ ∑' L' : {L' : List (Label × State) // L'.length = L.length}, esc pe s L'.1 :=
          ENNReal.le_tsum (⟨L, rfl⟩ : {L' : List (Label × State) // L'.length = L.length})
      _ ≤ ∑' s' : State,
            ∑' L' : {L' : List (Label × State) // L'.length = L.length}, esc pe s' L'.1 :=
          ENNReal.le_tsum s
  rw [Lk_const pe hAS L.length] at hbound
  exact nonpos_iff_eq_zero.mp hbound

/-- The `ofList`-form halt-below identity. -/
private theorem escP_eq_escHB {State Label : Type} {sys : System State Label}
    (pe : ProbabilisticExecution sys)
    (hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
              pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1)
    (s : State) (L : List (Label × State)) :
    escP pe s L = escHB pe s L := by
  have h0 : escP pe s L - escHB pe s L = 0 := esc_zero pe hAS s L
  exact le_antisymm (tsub_eq_zero_iff_le.mp h0) (escHB_le_escP pe s L)

/-- **Halt-below identity.** Under almost-sure halting (`hAS`), the probability of
a terminating execution equals the total halt mass over its finite continuations. -/
theorem ProbabilisticExecution.probOf_eq_haltBelow {State Label : Type}
    {sys : System State Label} (pe : ProbabilisticExecution sys)
    (hAS : (∑' g : {g : AlterSeq State Label // g.trans.Terminates},
              pe.probOf g.1 g.2 * pe.scheduler.next g.1 none) = 1)
    (e : AlterSeq State Label) (h : e.trans.Terminates) :
    pe.probOf e h = pe.haltBelow e h := by
  set L := e.trans.toList h with hL
  have heq : (Seq.ofList L : Seq (Label × State)) = e.trans := Stream'.Seq.ofList_toList e.trans h
  have hprob : pe.probOf e h = escP pe e.init L :=
    pe.probOf_congr e ⟨e.init, Seq.ofList L⟩ (by rw [heq]) h (Stream'.Seq.terminates_ofList L)
  have hhb : pe.haltBelow e h = escHB pe e.init L := by
    unfold ProbabilisticExecution.haltBelow escHB
    refine tsum_congr fun t => ?_
    have happ : e.trans.append (Seq.ofList t) = Seq.ofList (L ++ t) := by
      rw [Stream'.Seq.ofList_append, heq]
    unfold haltNode escP
    rw [pe.probOf_congr ⟨e.init, e.trans.append (Seq.ofList t)⟩ ⟨e.init, Seq.ofList (L ++ t)⟩
        (by rw [happ]) (append_ofList_terminates h t) (Stream'.Seq.terminates_ofList _),
      show pe.scheduler.next ⟨e.init, e.trans.append (Seq.ofList t)⟩ none
        = pe.scheduler.next ⟨e.init, Seq.ofList (L ++ t)⟩ none from by rw [happ]]
  rw [hprob, hhb]
  exact escP_eq_escHB pe hAS e.init L

end PLTS
