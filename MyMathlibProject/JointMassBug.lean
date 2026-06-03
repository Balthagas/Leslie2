/-
Concrete PLTS example pinpointing the `joint_mass_path` divergence bug.

We construct:
* a trivial concrete PLTS `sys_C` (one state, one external label `()`,
  step relation `μ_C = PMF.pure ()`);
* a trivial abstract PLTS `sys_A` on ℕ with one external label and
  every step `True`;
* the trivial relation `R s_C μ_A := True`;
* a probabilistic forward simulation `sim` returning the Dirac on the
  current abstract distribution;
* a probabilistic execution `pe_C` whose scheduler always issues
  `((), PMF.pure ())`;
* the initial abstract distribution `μ_A_init := PMF.pure 0`.

The bug: at step 1 in `joint_mass_path`, the inner sum

  ∑' (m_1 : MatchingState sim pe_C μ_A_init h_init_R),
    [m_1.e_C.init = () ∧
     m_1.e_C.trans = ⟨(), ()⟩ ∧
     m_1.μ_A_chain.length = 1]

is uncountable because `m_1.μ_A_chain : List (PMF ℕ)` of length 1 ranges
over `PMF ℕ`, which is infinite. So this sum equals `⊤`, and hence
`joint_mass_path m_0 [hC] [hA] = joint_kernel m_0 ... * ⊤ = ⊤`
whenever `joint_kernel m_0 ... > 0`.
-/

import MyMathlibProject.Simulation

open PLTS PMF Stream' Stream'.Seq
open scoped ENNReal

namespace JointMassBug

abbrev State_C := Unit
abbrev State_A := ℕ
abbrev Lab := Unit

/-- Concrete system: one state `()`, one (external) label, the only valid
step is the identity `() -[()]→ PMF.pure ()`. -/
def sys_C : LabelledSystem State_C Lab where
  toSystem := { init := (), step := fun _ _ μ => μ = PMF.pure () }
  internal := fun _ => False

/-- Abstract system on ℕ: every step `n -[()]→ μ` is allowed. -/
def sys_A : LabelledSystem State_A Lab where
  toSystem := { init := 0, step := fun _ _ _ => True }
  internal := fun _ => False

/-- Trivial relation. -/
def R : State_C → PMF State_A → Prop := fun _ _ => True

/-- A trivial product-like joint PMF: γ_{μ_C, μ_A} := μ_C.bind (fun a => μ_A.bind (fun b => pure (a, b))). -/
private noncomputable def trivialγ {α β : Type} (μ_C : PMF α) (μ_A : PMF β) :
    PMF (α × β) :=
  μ_C.bind (fun a => μ_A.bind (fun b => PMF.pure (a, b)))

private lemma trivialγ_fst {α β : Type} (μ_C : PMF α) (μ_A : PMF β) :
    PMF.map Prod.fst (trivialγ μ_C μ_A) = μ_C := by
  unfold trivialγ
  show PMF.map Prod.fst (μ_C.bind _) = μ_C
  rw [PMF.map_bind]
  -- ∀ a, (μ_A.bind (fun b => pure (a, b))).map Prod.fst = pure a
  have h : ∀ a : α, (μ_A.bind (fun b => (PMF.pure (a, b) : PMF (α × β)))).map Prod.fst = PMF.pure a := by
    intro a
    rw [PMF.map_bind]
    have h2 : ∀ b : β,
        ((PMF.pure (a, b) : PMF (α × β)).map Prod.fst : PMF α) = PMF.pure a := by
      intro b
      show ((PMF.pure (a, b) : PMF (α × β)).bind (PMF.pure ∘ Prod.fst) : PMF α) = PMF.pure a
      rw [PMF.pure_bind]
      rfl
    simp_rw [h2]
    exact PMF.bind_const _ _
  simp_rw [h]
  exact PMF.bind_pure _

private lemma trivialγ_snd {α β : Type} (μ_C : PMF α) (μ_A : PMF β) :
    PMF.map Prod.snd (trivialγ μ_C μ_A) = μ_A := by
  unfold trivialγ
  show PMF.map Prod.snd (μ_C.bind _) = μ_A
  rw [PMF.map_bind]
  have h : ∀ a : α, (μ_A.bind (fun b => (PMF.pure (a, b) : PMF (α × β)))).map Prod.snd = μ_A := by
    intro a
    rw [PMF.map_bind]
    have h2 : ∀ b : β,
        ((PMF.pure (a, b) : PMF (α × β)).map Prod.snd : PMF β) = PMF.pure b := by
      intro b
      show ((PMF.pure (a, b) : PMF (α × β)).bind (PMF.pure ∘ Prod.snd) : PMF β) = PMF.pure b
      rw [PMF.pure_bind]
      rfl
    simp_rw [h2]
    exact PMF.bind_pure _
  simp_rw [h]
  exact PMF.bind_const _ _

/-- hyperStep from `μ_A` back to itself at label `()`. -/
private lemma hyperStep_self (μ_A : PMF State_A) :
    hyperStep sys_A.toSystem μ_A () μ_A := by
  refine ⟨fun s => PMF.pure (PMF.pure s), ?_, ?_⟩
  · intro s _ μ' _; trivial
  · show μ_A = μ_A.bind (fun s => (PMF.pure (PMF.pure s)).bind id)
    simp

/-- weakStep self-loop on μ_A at label `()`. -/
private lemma weakStep_self (μ_A : PMF State_A) :
    weakStep sys_A μ_A () μ_A :=
  ⟨μ_A, μ_A, weakTau_refl _ _, hyperStep_self μ_A, weakTau_refl _ _⟩

/-- Simulation: at every step, return the Dirac on the input μ_A. -/
noncomputable def sim : ProbabilisticForwardSimulation sys_C sys_A R where
  init := ⟨PMF.pure 0, by
    intro s h_s
    rw [PMF.mem_support_pure_iff] at h_s
    exact h_s, trivial⟩
  step := fun _ μ_A _ _ μ_C _ => by
    refine ⟨PMF.pure μ_A, ?_, Or.inr ⟨id, ?_⟩⟩
    · -- PMFRel R μ_C (PMF.pure μ_A) via trivialγ μ_C (PMF.pure μ_A)
      refine ⟨trivialγ μ_C (PMF.pure μ_A), trivialγ_fst _ _, trivialγ_snd _ _, ?_⟩
      intros _ _; trivial
    · -- weakStep sys_A μ_A () ((PMF.pure μ_A).bind id) = weakStep sys_A μ_A () μ_A.
      have h : (PMF.pure μ_A).bind id = μ_A := by simp
      rw [h]
      exact weakStep_self μ_A

/-- The concrete execution: always schedule `((), PMF.pure ())`. -/
noncomputable def pe_C : ProbabilisticExecution sys_C.toSystem where
  initState := ()
  scheduler := {
    next := fun _ => some (PMF.pure ((), PMF.pure ()))
    valid := by
      intro e n s _ _ d h_d l μ h_μ
      have h_d_eq : d = PMF.pure ((), PMF.pure ()) := (Option.some.inj h_d).symm
      rw [h_d_eq, PMF.mem_support_pure_iff] at h_μ
      cases h_μ
      -- Goal: sys_C.toSystem.step s () (PMF.pure ()) — by definition this is `PMF.pure () = PMF.pure ()`.
      rfl
  }

/-- μ_A_init = Dirac at 0. -/
noncomputable def μ_A_init : PMF State_A := PMF.pure 0

/-- pe_C.init ⊆ R (trivial since R = True). -/
lemma h_init_R : ∀ s_C ∈ pe_C.init.support, R s_C μ_A_init := fun _ _ => trivial

/-- The initial matching state we'll evaluate joint_mass_path at. -/
noncomputable def m_0 : ProbabilisticForwardSimulation.MatchingState sim pe_C μ_A_init h_init_R :=
  ProbabilisticForwardSimulation.initial_matching_state sim pe_C μ_A_init h_init_R ()

/-- Witness injection: for each `μ : PMF ℕ`, build a matching state
satisfying the indicator. -/
private noncomputable def witness (μ : PMF State_A) :
    ProbabilisticForwardSimulation.MatchingState sim pe_C μ_A_init h_init_R where
  e_C := ⟨(), Seq.cons ((), ()) Seq.nil⟩
  e_C_term := ⟨1, rfl⟩
  μ_A_chain := [μ]
  h_R := fun _ => trivial

private lemma witness_injective : Function.Injective witness := by
  intro μ₁ μ₂ h
  have hkey := congr_arg
    (fun m : ProbabilisticForwardSimulation.MatchingState sim pe_C μ_A_init h_init_R =>
      m.μ_A_chain) h
  -- hkey : (witness μ₁).μ_A_chain = (witness μ₂).μ_A_chain, i.e., [μ₁] = [μ₂].
  exact List.head_eq_of_cons_eq hkey

/-- The witness always satisfies the canonical-extension indicator (it has
chain length 1 = m_0.chain.length + 1 and the right e_C). -/
private lemma witness_satisfies (μ : PMF State_A) :
    (witness μ).e_C.init = m_0.e_C.init ∧
    (witness μ).e_C.trans = m_0.e_C.trans.append (Seq.cons ((), ()) Seq.nil) ∧
    (witness μ).μ_A_chain.length = m_0.μ_A_chain.length + 1 := by
  refine ⟨rfl, ?_, rfl⟩
  change (Seq.cons ((), ()) Seq.nil) =
      (Stream'.Seq.nil : Seq (Lab × State_C)).append (Seq.cons ((), ()) Seq.nil)
  rw [Stream'.Seq.nil_append]

/-- `PMF ℕ` is infinite (PMF.pure is injective ℕ → PMF ℕ). -/
private instance : Infinite (PMF ℕ) :=
  Infinite.of_injective PMF.pure fun n m h => by
    have hkey := congr_arg (fun μ => μ n) h
    by_contra h_ne
    simp [PMF.pure_apply, h_ne] at hkey

/-- **The bug**: the indicator-sum at step 1 over `MatchingState`, with the
canonical-extension structural constraint, equals ⊤. The argument: there's
an injection `PMF ℕ → MatchingState ...` (the `witness` above) hitting only
m_next's satisfying the indicator. By `tsum_comp_le_tsum_of_injective`, the
m_next-sum is bounded below by `∑' (μ : PMF ℕ), 1 = ⊤`. -/
theorem indicator_sum_diverges :
    (∑' (m_next : ProbabilisticForwardSimulation.MatchingState sim pe_C μ_A_init h_init_R),
      (open Classical in
       if m_next.e_C.init = m_0.e_C.init ∧
          m_next.e_C.trans = m_0.e_C.trans.append (Seq.cons ((), ()) Seq.nil) ∧
          m_next.μ_A_chain.length = m_0.μ_A_chain.length + 1
        then (1 : ENNReal) else 0)) = ⊤ := by
  classical
  set indicator :
      ProbabilisticForwardSimulation.MatchingState sim pe_C μ_A_init h_init_R → ENNReal :=
    fun m_next =>
      if m_next.e_C.init = m_0.e_C.init ∧
         m_next.e_C.trans = m_0.e_C.trans.append (Seq.cons ((), ()) Seq.nil) ∧
         m_next.μ_A_chain.length = m_0.μ_A_chain.length + 1 then 1 else 0
  -- ∑' m, indicator m ≥ ∑' (μ : PMF ℕ), indicator (witness μ)
  have h_le : (∑' μ : PMF State_A, indicator (witness μ)) ≤ ∑' m, indicator m :=
    ENNReal.tsum_comp_le_tsum_of_injective witness_injective indicator
  -- indicator (witness μ) = 1 for every μ.
  have h_eq : ∀ μ, indicator (witness μ) = 1 := fun μ => if_pos (witness_satisfies μ)
  simp_rw [h_eq] at h_le
  -- ∑' (μ : PMF ℕ), 1 = ⊤
  have h_top : (∑' _ : PMF State_A, (1 : ENNReal)) = ⊤ :=
    ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero
  rw [h_top] at h_le
  exact top_le_iff.mp h_le

end JointMassBug
