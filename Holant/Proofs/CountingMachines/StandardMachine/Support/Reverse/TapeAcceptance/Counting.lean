import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.Staging.Source
import Holant.Proofs.CountingMachines.StandardMachine.Support.Reverse.TapeAcceptance.Simulation

set_option backward.isDefEq.respectTransparency false
/-! Locally checked adaptation of the frozen reference proof. The actual observer gives the previously missing
accepting-control producer. Both paths use exactly the same token vector,
including every deterministic edge and canonical held-halt none token. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
open Turing Computability Holant.Complexity
variable (m : BinaryMachine) (trueSymbol : m.core.Γ m.core.k₁)
local instance : Fintype m.core.K := m.core.kFin
local instance : Fintype m.core.Λ := m.core.ΛFin
local instance : Fintype m.core.σ := m.core.σFin
local instance (k : m.core.K) : Fintype (m.core.Γ k) := m.alphabets k

abbrev TapePath (n : ℕ) (c : m.Config) :=
  {tokens : Fin n → Option Bool //
    m.TraceValid (List.ofFn tokens) c (haltList m.core [trueSymbol])}

noncomputable instance tapePathFintype (n : ℕ) (c : m.Config) :
    Fintype (TapePath m trueSymbol n c) := by
  classical
  unfold TapePath
  infer_instance

def tapeToControl (n : ℕ) (c : m.Config) :
    TapePath m trueSymbol n c → Staging.Program.AcceptedPath (machine m trueSymbol)
      (acceptControl m) n (liftCfg m trueSymbol c) := fun p =>
  ⟨p.val,(accepts_trace_iff m trueSymbol (List.ofFn p.val) c).mpr p.property⟩

def controlToTape (n : ℕ) (c : m.Config) :
    Staging.Program.AcceptedPath (machine m trueSymbol) (acceptControl m) n
      (liftCfg m trueSymbol c) → TapePath m trueSymbol n c := fun p =>
  ⟨p.val,(accepts_trace_iff m trueSymbol (List.ofFn p.val) c).mp p.property⟩

/-- Identity on actual tokens, not merely a cardinality argument. The
observer's deterministic Bool branches never become nondeterministic splits. -/
def tapeControlEquiv (n : ℕ) (c : m.Config) :
    TapePath m trueSymbol n c ≃ Staging.Program.AcceptedPath (machine m trueSymbol)
      (acceptControl m) n (liftCfg m trueSymbol c) where
  toFun := tapeToControl m trueSymbol n c
  invFun := controlToTape m trueSymbol n c
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

def tapeCount {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))
    (T : Polynomial ℕ) (a : α) : ℕ :=
  Fintype.card (TapePath m trueSymbol (T.eval (ea.encode a).length) (initList m.core (ea.encode a)))

theorem tape_count {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))
    (T : Polynomial ℕ) (a : α) :
    tapeCount m trueSymbol ea T a =
      Staging.Program.pathCount (machine m trueSymbol) (acceptControl m) ea T a := by
  unfold tapeCount Staging.Program.pathCount
  rw [← lift_init m trueSymbol]
  exact Fintype.card_congr (tapeControlEquiv m trueSymbol _ _)

def acceptedEquiv {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))
    (T : Polynomial ℕ) (a : α) :
    Staging.Program.AcceptedBits (machine m trueSymbol) (acceptControl m)
      (T.eval (ea.encode a).length) (initList (computer m trueSymbol) (ea.encode a)) ≃
        TapePath m trueSymbol (T.eval (ea.encode a).length) (initList m.core (ea.encode a)) :=
  (Staging.Program.acceptedEquiv (machine m trueSymbol) (acceptControl m) _ _).trans
    (by simpa only [lift_init] using
      (tapeControlEquiv m trueSymbol (T.eval (ea.encode a).length)
        (initList m.core (ea.encode a))).symm)

/-- All actual verifier fields are reused. Only the count field is transported
through the proved original-tape/produced-control path equivalence. -/
def reverseWitness {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))
    (T : Polynomial ℕ) : SharpPWitness ea (tapeCount m trueSymbol ea T) where
  witnessLength := (Staging.Source.reverseWitness (machine m trueSymbol) T (acceptControl m) ea).witnessLength
  accept := (Staging.Source.reverseWitness (machine m trueSymbol) T (acceptControl m) ea).accept
  verifier := (Staging.Source.reverseWitness (machine m trueSymbol) T (acceptControl m) ea).verifier
  counts a := (tape_count m trueSymbol ea T a).trans
    ((Staging.Source.reverseWitness (machine m trueSymbol) T (acceptControl m) ea).counts a)

theorem bounded_inSharpP {α : Type} (ea : Encoding α (m.core.Γ m.core.k₀))
    (T : Polynomial ℕ) : InSharpP ea (tapeCount m trueSymbol ea T) :=
  ⟨reverseWitness m trueSymbol ea T⟩

/-- The existing real raw-input verifier now reads acceptance from actual
original tapes, with no supplied accepting table on original states. -/
theorem physical_accepts_iff (T : Polynomial ℕ) (word : List (m.core.Γ m.core.k₀))
    (bits : List Bool) :
    (∃ t, (fun p => p.bind
      (Staging.Source.machine (machine m trueSymbol) T (acceptControl m)).step)^[t]
      (some (initList (Staging.Source.machine (machine m trueSymbol) T (acceptControl m))
        (word.map Sum.inl++bits.map Sum.inr))) =
      some (haltList (Staging.Source.machine (machine m trueSymbol) T (acceptControl m))
        [Sum.inr true])) ↔
      ∃ tokens, tokens.length = T.eval word.length ∧ bits = tokens.flatMap Packet.encode ∧
        m.TraceValid tokens (initList m.core word) (haltList m.core [trueSymbol]) := by
  rw [Staging.Source.physical_accepts_iff]
  constructor
  · rintro ⟨tokens,d,hlen,hbits,ht,hl,hv⟩
    refine ⟨tokens,hlen,hbits,?_⟩
    exact (accepts_trace_iff m trueSymbol tokens (initList m.core word)).mp
      ⟨d,by simpa only [lift_init] using ht,hl,hv⟩
  · rintro ⟨tokens,hlen,hbits,ht⟩
    obtain ⟨d,hd,hl,hv⟩ :=
      (accepts_trace_iff m trueSymbol tokens (initList m.core word)).mpr ht
    exact ⟨tokens,d,hlen,hbits,by simpa only [lift_init] using hd,hl,hv⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.StandardMachine.Support.Reverse.TapeAcceptance.Program
