import Holant.Proofs.Hardness.PairedPinsCompiler
import Holant.Proofs.Hardness.PairedPinsSemantics

/-! The physical pairing programme on its true domain: original validated
records with equal numbers of the two unary endpoints. Its parser checks that
condition, and its exact output is the validated original-plus-one-binary graph.
Balance here is an intermediate graph-domain property. A hardness source must
prove it for its own emitted graphs; this module does not assume that source
producer or a desired hardness result. -/
set_option maxRecDepth 32768
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsValidated
open Computability Holant Holant.Complexity BinaryCompose FixedFieldMachines
open PairedPinsRaw

abbrev Input (s b : ℕ) (a : ℕ → ℕ) :=
  {r : RawClosedNetwork // r.WellFormed (s+2) b (sourceArity s a) ∧ Balanced s r}

instance balancedDecidable (s : ℕ) (r : RawClosedNetwork) : Decidable (Balanced s r) :=
  inferInstanceAs (Decidable ((pins s false r).length=(pins s true r).length))

def inputEncoding (s b : ℕ) (a : ℕ → ℕ) : Encoding (Input s b a) Bool where
  encode r := RawClosedNetwork.encoding.encode r.val
  decode bits := do
    let r ← RawClosedNetwork.encoding.decode bits
    if h : r.WellFormed (s+2) b (sourceArity s a) ∧ Balanced s r then some ⟨r,h⟩ else none
  decode_encode r := by simp [RawClosedNetwork.encoding.decode_encode,r.property]

abbrev targetEncoding (s b : ℕ) (a : ℕ → ℕ) :=
  RawClosedNetwork.validatedEncoding (s+1) b (targetArity s a)

def query {s b : ℕ} {a : ℕ → ℕ} (r : Input s b a) :
    {q : RawClosedNetwork // q.WellFormed (s+1) b (targetArity s a)} :=
  ⟨raw s r.val,PairedPinsSemantics.wellFormed r.property.1 r.property.2⟩

/-- Retyping the exact output of the physical parser/emitter changes neither
its program, clock nor a single input/output bit. -/
def computes (s b : ℕ) (a : ℕ → ℕ) :
    Computes (inputEncoding s b a) (targetEncoding s b a) query :=
  recode (PairedPinsCompiler.computes s) Subtype.val (fun _ => rfl) (fun _ => rfl)

theorem query_bytes {s b : ℕ} {a : ℕ → ℕ} (r : Input s b a) :
    (targetEncoding s b a).encode (query r)=RawClosedNetwork.encoding.encode (raw s r.val) := rfl

theorem query_parses {s b : ℕ} {a : ℕ → ℕ} (r : Input s b a) :
    (targetEncoding s b a).decode (RawClosedNetwork.encoding.encode (raw s r.val))=
      some (query r) :=
  (targetEncoding s b a).decode_encode (query r)

def outputs {s b : ℕ} {a : ℕ → ℕ} (r : Input s b a) :
    Turing.TM2OutputsInTime (computes s b a).machine.computer ((inputEncoding s b a).encode r)
      (some ((targetEncoding s b a).encode (query r)))
      ((computes s b a).time.eval ((inputEncoding s b a).encode r).length) :=
  (computes s b a).outputs r

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PairedPinsValidated
