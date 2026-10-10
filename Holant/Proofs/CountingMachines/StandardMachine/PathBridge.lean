import Holant.Proofs.CountingMachines.StandardMachine.StackSimulation
import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Counting

set_option backward.isDefEq.respectTransparency false
/-! Exact accepted-path transport. No terminal-configuration quotient is used:
both path types retain the full edge-label word. The sole new edge is the
mandatory deterministic input-load edge. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
open Turing Computability Holant.Complexity
namespace Model
variable {Γ Q : Type} [Fintype Γ] [Fintype Q] (m : Model Γ Q)
local instance : Fintype (m.toBinary.core.Γ m.toBinary.core.k₀) := inferInstanceAs (Fintype Γ)

private def listFunction {A : Type} {n : ℕ} (xs : List A) (h : xs.length = n) : Fin n → A :=
  fun i => xs.get ⟨i.val, by rw [h]; exact i.isLt⟩

private theorem listFunction_word {A : Type} {n : ℕ} (xs : List A) (h : xs.length = n) :
    List.ofFn (listFunction xs h) = xs := by
  apply List.ext_getElem
  · rw [List.length_ofFn, h]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

abbrev CompiledPath (n : ℕ) (word : List Γ) :=
  Support.Reverse.Staging.Program.AcceptedPath m.toBinary m.acceptControl
    (n + 1) (initList m.computer word)

/-- A successful compiled path has one mandatory initial None edge, followed
by precisely the original labels; arbitrary target endpoints are recovered. -/
theorem compiled_accepts_iff (tokens : List (Option Bool)) (word : List Γ) :
    (∃ finish : m.toBinary.Config,
      m.toBinary.TraceValid tokens (initList m.computer word) finish ∧
        finish.l = none ∧ m.acceptControl finish.var = true) ↔
    ∃ rest, tokens = none :: rest ∧ ∃ finish : Config Γ Q,
      m.Accepts finish ∧ m.Trace rest (m.initialConfig word) finish := by
  cases tokens with
  | nil =>
      constructor
      · rintro ⟨finish, ht, hl, _⟩
        change initList m.computer word = finish at ht
        subst finish
        simp [initList] at hl
      · rintro ⟨_, h, _⟩; cases h
  | cons token rest =>
      constructor
      · rintro ⟨finish, ⟨next, hs, ht⟩, hl, ha⟩
        cases token with
        | some bit => rw [m.initialize_no_choice] at hs; cases hs
        | none =>
            rw [m.initialize_step] at hs
            have hn := Option.some.inj hs
            subst next
            obtain ⟨d, hd, hr⟩ := m.trace_lift rest (m.initialConfig word) finish ht
            subst finish
            exact ⟨rest, rfl, d, (m.accepts_embed d).mp ⟨hl, ha⟩, hr⟩
      · rintro ⟨tail, he, finish, ha, ht⟩
        have htoken : token = none := (List.cons.inj he).1
        have htail : rest = tail := (List.cons.inj he).2
        subst token; subst tail
        have haccept := (m.accepts_embed finish).mpr ha
        exact ⟨m.embed finish, ⟨m.embed (m.initialConfig word), m.initialize_step word,
          (m.trace_embed rest _ finish).mpr ht⟩, haccept.1, haccept.2⟩

def compilePath (n : ℕ) (word : List Γ) (p : m.AcceptedPath n word) : m.CompiledPath n word :=
  ⟨listFunction (none :: p.val) (by simp [p.property.1]), by
    rw [listFunction_word]
    exact (m.compiled_accepts_iff _ word).mpr ⟨p.val, rfl, p.property.2⟩⟩

theorem compilePath_word (n : ℕ) (word : List Γ) (p : m.AcceptedPath n word) :
    List.ofFn (m.compilePath n word p).val = none :: p.val := by
  exact listFunction_word (none :: p.val) (by simp [p.property.1])

def recoverPath (n : ℕ) (word : List Γ) (p : m.CompiledPath n word) : m.AcceptedPath n word :=
  ⟨(List.ofFn p.val).tail, by
    obtain ⟨rest, he, finish, ha, ht⟩ := (m.compiled_accepts_iff _ word).mp p.property
    constructor
    · have hl := congrArg List.length he
      simp only [List.length_ofFn, List.length_cons] at hl
      rw [he, List.tail_cons]
      omega
    · rw [he, List.tail_cons]
      exact ⟨finish, ha, ht⟩⟩

/-- Explicit forward and reverse functions preserve the literal branch words. -/
def acceptedPathEquiv (n : ℕ) (word : List Γ) : m.AcceptedPath n word ≃ m.CompiledPath n word where
  toFun := m.compilePath n word
  invFun := m.recoverPath n word
  left_inv p := by
    apply Subtype.ext
    change (List.ofFn (m.compilePath n word p).val).tail = p.val
    rw [compilePath_word, List.tail_cons]
  right_inv p := by
    apply Subtype.ext
    apply List.ofFn_injective
    rw [compilePath_word]
    obtain ⟨rest, he, _⟩ := (m.compiled_accepts_iff _ word).mp p.property
    change none :: (List.ofFn p.val).tail = List.ofFn p.val
    rw [he, List.tail_cons]

noncomputable instance acceptedPathFintype (n : ℕ) (word : List Γ) : Fintype (m.AcceptedPath n word) :=
  Fintype.ofEquiv (m.CompiledPath n word) (m.acceptedPathEquiv n word).symm

def pathCount {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ) (a : α) : ℕ :=
  Fintype.card (m.AcceptedPath (clock.eval (ea.encode a).length) (ea.encode a))

theorem compiled_count {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ) (a : α) :
    Support.Reverse.Staging.Program.pathCount m.toBinary m.acceptControl ea (clock + 1) a =
      m.pathCount ea clock a := by
  unfold Support.Reverse.Staging.Program.pathCount pathCount
  simp only [Polynomial.eval_add, Polynomial.eval_one]
  convert Fintype.card_congr (m.acceptedPathEquiv (clock.eval (ea.encode a).length) (ea.encode a)).symm using 1 <;> rfl

/-- Reverse conversion from the independent finite move/write model to an
actual finite SharpPWitness verifier. Its packet interpreter, physical unary
clock and cleanup program are constructed, not supplied as hypotheses. -/
def standardToWitness {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ) :
    SharpPWitness ea (m.pathCount ea clock) where
  witnessLength := 2 * (clock + 1)
  accept := (Support.Reverse.Staging.Program.sharpPWitness m.toBinary m.acceptControl ea (clock + 1)).accept
  verifier := (Support.Reverse.Staging.Program.sharpPWitness m.toBinary m.acceptControl ea (clock + 1)).verifier
  counts a := (m.compiled_count ea clock a).symm.trans
    ((Support.Reverse.Staging.Program.sharpPWitness m.toBinary m.acceptControl ea (clock + 1)).counts a)

theorem bounded_inSharpP {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ) :
    InSharpP ea (m.pathCount ea clock) := ⟨m.standardToWitness ea clock⟩

/-- The equivalence is with exactly the accepted Boolean packet witnesses of
the constructed verifier. No unused choice bits or alternative padding occur. -/
def acceptedWitnessEquiv (n : ℕ) (word : List Γ) :
    Support.Reverse.Staging.Program.AcceptedBits m.toBinary m.acceptControl (n + 1)
      (initList m.computer word) ≃ m.AcceptedPath n word :=
  (Support.Reverse.Staging.Program.acceptedEquiv m.toBinary m.acceptControl (n + 1)
    (initList m.computer word)).trans (m.acceptedPathEquiv n word).symm

end Model
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
