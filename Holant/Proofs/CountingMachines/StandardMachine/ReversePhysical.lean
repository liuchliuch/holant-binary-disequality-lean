import Holant.Proofs.CountingMachines.StandardMachine.PathBridge
import Holant.Proofs.CountingMachines.StandardMachine.CanonicalPaths

set_option backward.isDefEq.respectTransparency false
/-! The reverse bridge counts all physical accepting computations, rather than
only a caller-chosen collection of bounded histories. The sole time premise is
legitimate membership data for the independent source machine, on the literal
encoded inputs at issue. The generated verifier and all its costs remain the
constructed packet interpreter. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
open Turing Computability Holant.Complexity
namespace Model
variable {Γ Q : Type} [Fintype Γ] [Fintype Q] (m : Model Γ Q)

/-- An encoded input has exactly its actual finite labelled accepting paths.
No quotient by endpoint or internal configurations is taken. -/
def physicalCount {α : Type} (ea : Encoding α Γ) (a : α) : ℕ :=
  Nat.card (m.PhysicalPath (ea.encode a))

def physicalPathEquivAt (clock : Polynomial ℕ) (word : List Γ)
    (htime : ∀ tokens finish, m.PhysicalTrace tokens (m.initialConfig word) finish →
      tokens.length ≤ clock.eval word.length) :
    m.PhysicalPath word ≃ m.AcceptedPath (clock.eval word.length) word :=
  (show m.PhysicalPath word ≃ m.ShortPhysicalPath (clock.eval word.length) word from
    { toFun := fun p => ⟨p.val, by
        obtain ⟨finish, ha, ht⟩ := p.property
        exact ⟨htime p.val finish ht, finish, ha, ht⟩⟩
      invFun := fun p => ⟨p.val, p.property.2⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext rfl }).trans
    (m.physicalPathEquiv (clock.eval word.length) word)

theorem physicalCount_eq {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ) (a : α)
    (htime : ∀ tokens finish, m.PhysicalTrace tokens (m.initialConfig (ea.encode a)) finish →
      tokens.length ≤ clock.eval (ea.encode a).length) :
    m.physicalCount ea a = m.pathCount ea clock a := by
  unfold physicalCount pathCount
  rw [Nat.card_congr (m.physicalPathEquivAt clock (ea.encode a) htime)]
  exact Nat.card_eq_fintype_card

/-- All ordinary physical accepting paths give exactly the accepting witnesses
of an internally generated polynomial-time verifier on the original encoding. -/
def physicalToWitness {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ)
    (htime : ∀ a tokens finish,
      m.PhysicalTrace tokens (m.initialConfig (ea.encode a)) finish →
        tokens.length ≤ clock.eval (ea.encode a).length) :
    SharpPWitness ea (m.physicalCount ea) where
  witnessLength := (m.standardToWitness ea clock).witnessLength
  accept := (m.standardToWitness ea clock).accept
  verifier := (m.standardToWitness ea clock).verifier
  counts a := (m.physicalCount_eq ea clock a (htime a)).trans
    ((m.standardToWitness ea clock).counts a)

theorem physical_inSharpP {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ)
    (htime : ∀ a tokens finish,
      m.PhysicalTrace tokens (m.initialConfig (ea.encode a)) finish →
        tokens.length ≤ clock.eval (ea.encode a).length) :
    InSharpP ea (m.physicalCount ea) := ⟨m.physicalToWitness ea clock htime⟩

/-- This equivalence composes the forced canonical padding with the literal
packet parser bijection. Short runs, deterministic rows and early halts have
one representation; every real split keeps its selected Boolean label. -/
def physicalWitnessEquiv (clock : Polynomial ℕ) (word : List Γ)
    (htime : ∀ tokens finish, m.PhysicalTrace tokens (m.initialConfig word) finish →
      tokens.length ≤ clock.eval word.length) :
    m.PhysicalPath word ≃
      Support.Reverse.Staging.Program.AcceptedBits m.toBinary m.acceptControl
        (clock.eval word.length + 1) (initList m.computer word) :=
  (m.physicalPathEquivAt clock word htime).trans
    (m.acceptedWitnessEquiv (clock.eval word.length) word).symm

private def witnessCast {n k : ℕ} (h : n = k) (A : List Bool → Bool) :
    {x : Fin n → Bool // A (List.ofFn x) = true} ≃
      {x : Fin k → Bool // A (List.ofFn x) = true} where
  toFun x := ⟨fun i => x.val (Fin.cast h.symm i),by
    rw [← List.ofFn_congr h x.val]
    exact x.property⟩
  invFun x := ⟨fun i => x.val (Fin.cast h i),by
    rw [← List.ofFn_congr h.symm x.val]
    exact x.property⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (by apply Fin.ext; rfl)
  right_inv x := by
    apply Subtype.ext
    funext i
    exact congrArg x.val (by apply Fin.ext; rfl)

/-- This is the actual accepted-witness subtype of the constructed verifier,
with its own polynomial length and its actual acceptance function. -/
def verifierWitnessEquiv {α : Type} (ea : Encoding α Γ) (clock : Polynomial ℕ)
    (htime : ∀ a tokens finish,
      m.PhysicalTrace tokens (m.initialConfig (ea.encode a)) finish →
        tokens.length ≤ clock.eval (ea.encode a).length) (a : α) :
    m.PhysicalPath (ea.encode a) ≃
      {bits : Fin ((m.physicalToWitness ea clock htime).witnessLength.eval
          (ea.encode a).length) → Bool //
        (m.physicalToWitness ea clock htime).accept (a,List.ofFn bits) = true} := by
  change m.PhysicalPath (ea.encode a) ≃
    {bits : Fin ((2 * (clock + 1)).eval (ea.encode a).length) → Bool //
      Support.Reverse.Staging.Program.packetEval m.toBinary m.acceptControl
        ((clock + 1).eval (ea.encode a).length) (List.ofFn bits)
        (initList m.computer (ea.encode a)) = true}
  have hp : (clock + 1).eval (ea.encode a).length = clock.eval (ea.encode a).length + 1 := by simp
  rw [hp]
  have hlen : 2 * (clock.eval (ea.encode a).length + 1) =
      (2 * (clock + 1)).eval (ea.encode a).length := by
    simp only [Polynomial.eval_mul,Polynomial.eval_ofNat,hp]
  exact (m.physicalWitnessEquiv clock (ea.encode a) (htime a)).trans (witnessCast hlen (fun bits => Support.Reverse.Staging.Program.packetEval
      m.toBinary m.acceptControl (clock.eval (ea.encode a).length + 1) bits
        (initList m.computer (ea.encode a))))

end Model
end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine
