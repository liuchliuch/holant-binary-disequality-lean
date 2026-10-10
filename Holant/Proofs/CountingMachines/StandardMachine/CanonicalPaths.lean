import Holant.Proofs.CountingMachines.StandardMachine.Model

set_option backward.isDefEq.respectTransparency false
/-! The padded path convention counts exactly the ordinary accepting physical
computations. Every early halt receives one forced None suffix; its stopping
time is recovered from the first halted control and is never a free witness. -/
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
namespace Model
variable {Γ Q : Type} (m : Model Γ Q)

/-- Remove only padding after the first stopped control. Invalid words need
not acquire any accepting meaning: theorems below require real step equations. -/
def stripPadding : List (Option Bool) → Config Γ Q → List (Option Bool)
  | [], _ => []
  | token :: rest, c =>
      if (m.verdict c.control).isSome then [] else
        match m.step token c with
        | none => []
        | some next => token :: stripPadding rest next

theorem physicalStep_eq (token : Option Bool) (c d : Config Γ Q)
    (h : m.physicalStep token c = some d) :
    m.verdict c.control = none ∧ m.step token c = some d := by
  cases hv : m.verdict c.control with
  | none => exact ⟨rfl, by simpa [physicalStep, hv] using h⟩
  | some b => simp [physicalStep, hv] at h

theorem physicalTrace_trace (tokens : List (Option Bool)) (c d : Config Γ Q)
    (h : m.PhysicalTrace tokens c d) : m.Trace tokens c d := by
  induction tokens generalizing c with
  | nil => exact h
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := h
      exact ⟨next, (m.physicalStep_eq token c next hs).2, ih next ht⟩

theorem strip_physical (tokens : List (Option Bool)) (c d : Config Γ Q)
    (h : m.PhysicalTrace tokens c d) : m.stripPadding tokens c = tokens := by
  induction tokens generalizing c with
  | nil => rfl
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := h
      obtain ⟨hv, he⟩ := m.physicalStep_eq token c next hs
      simp [stripPadding, hv, he, ih next ht]

theorem strip_after_halt (tokens : List (Option Bool)) (c : Config Γ Q) (b : Bool)
    (h : m.verdict c.control = some b) : m.stripPadding tokens c = [] := by
  cases tokens <;> simp [stripPadding, h]

/-- The exact word is recovered, including all deterministic and split labels
before halt, and the unique number of forced padding tokens afterward. -/
theorem strip_spec (tokens : List (Option Bool)) (c d : Config Γ Q)
    (h : m.Trace tokens c d) (ha : m.Accepts d) :
    m.PhysicalTrace (m.stripPadding tokens c) c d ∧
      tokens = m.stripPadding tokens c ++
        List.replicate (tokens.length - (m.stripPadding tokens c).length) none := by
  induction tokens generalizing c with
  | nil => exact ⟨h, rfl⟩
  | cons token rest ih =>
      cases hv : m.verdict c.control with
      | some b =>
          obtain ⟨hw, he⟩ := (m.trace_halted (token :: rest) c d b hv).mp h
          subst d
          simpa only [strip_after_halt m _ c b hv, List.length_nil, Nat.sub_zero,
            List.nil_append, PhysicalTrace] using And.intro (rfl : c = c) hw
      | none =>
          obtain ⟨next, hs, ht⟩ := h
          obtain ⟨hphysical, hword⟩ := ih next ht
          have hstrip : m.stripPadding (token :: rest) c = token :: m.stripPadding rest next := by
            simp [stripPadding, hv, hs]
          constructor
          · rw [hstrip]
            exact ⟨next, by simpa [physicalStep, hv] using hs, hphysical⟩
          · rw [hstrip]
            simpa only [List.length_cons, Nat.add_sub_add_right, List.cons_append] using
              congrArg (token :: ·) hword

/-- Padding an actual accepting computation never adds a choice or changes
its final configuration. -/
theorem pad_physical (tokens : List (Option Bool)) (c d : Config Γ Q) (n : ℕ)
    (h : m.PhysicalTrace tokens c d) (ha : m.Accepts d) :
    m.Trace (tokens ++ List.replicate n none) c d :=
  m.trace_append tokens _ c d d (m.physicalTrace_trace tokens c d h)
    (m.canonical_padding n d true ha)

theorem strip_padded (tokens : List (Option Bool)) (c d : Config Γ Q) (n : ℕ)
    (h : m.PhysicalTrace tokens c d) (ha : m.Accepts d) :
    m.stripPadding (tokens ++ List.replicate n none) c = tokens := by
  induction tokens generalizing c with
  | nil =>
      change c = d at h
      subst d
      exact m.strip_after_halt _ c true ha
  | cons token rest ih =>
      obtain ⟨next, hs, ht⟩ := h
      obtain ⟨hv, he⟩ := m.physicalStep_eq token c next hs
      simp [stripPadding, hv, he, ih next ht]

def ShortPhysicalPath (n : ℕ) (word : List Γ) :=
  {tokens : List (Option Bool) // tokens.length ≤ n ∧
    ∃ finish, m.Accepts finish ∧ m.PhysicalTrace tokens (m.initialConfig word) finish}

def padPath (n : ℕ) (word : List Γ) (p : m.ShortPhysicalPath n word) : m.AcceptedPath n word :=
  ⟨p.val ++ List.replicate (n - p.val.length) none, by
    constructor
    · have hp := p.property.1
      simp only [List.length_append, List.length_replicate]
      omega
    · obtain ⟨finish, ha, ht⟩ := p.property.2
      exact ⟨finish, ha, m.pad_physical p.val _ finish _ ht ha⟩⟩

def stripPath (n : ℕ) (word : List Γ) (p : m.AcceptedPath n word) : m.ShortPhysicalPath n word :=
  ⟨m.stripPadding p.val (m.initialConfig word), by
    obtain ⟨finish, ha, ht⟩ := p.property.2
    obtain ⟨hp, hw⟩ := m.strip_spec p.val _ finish ht ha
    refine ⟨?_, finish, ha, hp⟩
    have hl := congrArg List.length hw
    simp only [List.length_append, List.length_replicate, p.property.1] at hl
    omega⟩

def physicalPathEquiv (n : ℕ) (word : List Γ) : m.ShortPhysicalPath n word ≃ m.AcceptedPath n word where
  toFun := m.padPath n word
  invFun := m.stripPath n word
  left_inv p := by
    apply Subtype.ext
    obtain ⟨finish, ha, ht⟩ := p.property.2
    exact m.strip_padded p.val _ finish _ ht ha
  right_inv p := by
    apply Subtype.ext
    obtain ⟨finish, ha, ht⟩ := p.property.2
    have hw := (m.strip_spec p.val _ finish ht ha).2
    change m.stripPadding p.val (m.initialConfig word) ++
      List.replicate (n - (m.stripPadding p.val (m.initialConfig word)).length) none = p.val
    simpa only [p.property.1] using hw.symm

abbrev PhysicalPath (word : List Γ) :=
  {tokens : List (Option Bool) // ∃ finish,
    m.Accepts finish ∧ m.PhysicalTrace tokens (m.initialConfig word) finish}

/-- With legitimate source polynomial-time data, every ordinary accepting
computation is included and exactly one padded representative is counted. -/
def allPhysicalPathEquiv (clock : Polynomial ℕ) (htime : m.PolyTime clock) (word : List Γ) :
    m.PhysicalPath word ≃ m.AcceptedPath (clock.eval word.length) word :=
  (show m.PhysicalPath word ≃ m.ShortPhysicalPath (clock.eval word.length) word from
    { toFun := fun p => ⟨p.val, by
        obtain ⟨finish, ha, ht⟩ := p.property
        exact ⟨htime word p.val finish ht, finish, ha, ht⟩⟩
      invFun := fun p => ⟨p.val, p.property.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }).trans
    (m.physicalPathEquiv (clock.eval word.length) word)

end Model
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
