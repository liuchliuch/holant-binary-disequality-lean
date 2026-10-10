import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.TapeAcceptance.Resources

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. Concrete consumer of the existing forward witness
machine. Its accepting terminal is the actual encoded Bool true with reset
state and clean tapes. No accepting-control equivalence is supplied as input. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Forward
open Turing Computability Holant.Complexity
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

abbrev original := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.machine w
def trueSymbol : (original w).core.Γ (original w).core.k₁ :=
  w.verifier.outputAlphabet.symm (Sum.inr true)
abbrev observed := Program.machine (original w) (trueSymbol w)
abbrev clock := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.timePolynomial w

def vector (a : α) (tokens : List (Option Bool))
    (hlen : tokens.length = Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a) :
    Fin (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a) → Option Bool :=
  fun i => tokens.get ⟨i.val,by rw [hlen]; exact i.isLt⟩

theorem vector_word (a : α) (tokens : List (Option Bool))
    (hlen : tokens.length = Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a) :
    List.ofFn (vector w a tokens hlen) = tokens := by
  apply List.ext_getElem
  · rw [List.length_ofFn,hlen]
  · intro i hi hj
    rw [List.getElem_ofFn]
    rfl

/-- The list/vector change has no extension choices: it retains every token
and every halt-padding row of the original forward execution. -/
def tapePhysicalEquiv (a : α) :
    Program.TapePath (original w) (trueSymbol w)
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a) (initList (original w).core (ea.encode a)) ≃
        Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a where
  toFun p := ⟨List.ofFn p.val,List.length_ofFn,by
    simpa only [original,trueSymbol,WitnessMachine.terminal_eq_halt] using p.property⟩
  invFun p := ⟨vector w a p.val p.property.1,by
    rw [vector_word]
    simpa only [original,trueSymbol,WitnessMachine.terminal_eq_halt] using p.property.2⟩
  left_inv p := by
    apply Subtype.ext
    apply List.ofFn_injective
    simpa only using vector_word w a _ _
  right_inv p := by
    apply Subtype.ext
    simpa only using vector_word w a _ _

/-- The count law consumes the existing actual forward execution and path
bijection; no conventional #P hardness or machine equivalence is assumed. -/
theorem tape_count (a : α) : Program.tapeCount (original w) (trueSymbol w) ea (clock w) a = f a := by
  calc
    Program.tapeCount (original w) (trueSymbol w) ea (clock w) a =
      Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physicalCount w a :=
        Fintype.card_congr (tapePhysicalEquiv w a)
    _ = f a := Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.physical_count w a

def roundtripWitness : SharpPWitness ea f where
  witnessLength := (Program.reverseWitness (original w) (trueSymbol w) ea (clock w)).witnessLength
  accept := (Program.reverseWitness (original w) (trueSymbol w) ea (clock w)).accept
  verifier := (Program.reverseWitness (original w) (trueSymbol w) ea (clock w)).verifier
  counts a := (tape_count w a).symm.trans
    ((Program.reverseWitness (original w) (trueSymbol w) ea (clock w)).counts a)

/-- The actual staged verifier's fixed packets are in a two-way bijection
with the original accepted witnesses, via both actual machine presentations. -/
def acceptedWitnessEquiv (a : α) :
    Staging.Program.AcceptedBits (observed w) (Program.acceptControl (original w))
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.time w a)
      (initList (Program.computer (original w) (trueSymbol w)) (ea.encode a)) ≃
        Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.AcceptedWitness w a :=
  (Program.acceptedEquiv (original w) (trueSymbol w) ea (clock w) a).trans
    ((tapePhysicalEquiv w a).trans
      (Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.acceptedWitnessPhysicalEquiv w a).symm)

theorem physical_accepts_iff (a : α) (bits : List Bool) :
    (∃ t, (fun p => p.bind
      (Staging.Source.machine (observed w) (clock w) (Program.acceptControl (original w))).step)^[t]
      (some (initList
        (Staging.Source.machine (observed w) (clock w) (Program.acceptControl (original w)))
        ((ea.encode a).map Sum.inl++bits.map Sum.inr))) =
      some (haltList
        (Staging.Source.machine (observed w) (clock w) (Program.acceptControl (original w)))
        [Sum.inr true])) ↔
      ∃ p : Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Source.PhysicalPath w a,
        bits = p.val.flatMap Packet.encode := by
  rw [Program.physical_accepts_iff]
  constructor
  · rintro ⟨tokens,hlen,hbits,ht⟩
    exact ⟨⟨tokens,hlen,by simpa only [original,trueSymbol,WitnessMachine.terminal_eq_halt] using ht⟩,hbits⟩
  · rintro ⟨p,hbits⟩
    exact ⟨p.val,p.property.1,hbits,
      by simpa only [original,trueSymbol,WitnessMachine.terminal_eq_halt] using p.property.2⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Forward
