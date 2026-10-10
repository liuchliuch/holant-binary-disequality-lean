import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinarySquare
import Holant.Proofs.Tractability.AffineMachine.WireLists

/-! The actual finite byte programme duplicates the factor list while copying
the declared-variable header. Its validated output is the literal even-degree
instance and its exact partition is the squared original row partition. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySquareProgramme
open Holant Holant.Complexity Computability
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.TetrahedralCompletion.EvenCSPReduction
open StableHigherCurrentOrdinarySquare
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

abbrev variableEncoding := GraphPreprocessing.UnaryBinary.unaryEncoding
abbrev factorsEncoding := framedListEncoding Raw.factorEncoding

def variablesComputes : Computes Raw.encoding variableEncoding (fun r => r.variables) :=
  recode (Wiring.firstComputes variableEncoding factorsEncoding)
    (fun r => (r.variables,r.factors)) (fun _ => rfl) (fun _ => rfl)

def factorsComputes : Computes Raw.encoding factorsEncoding (fun r => r.factors) :=
  recode (Wiring.secondComputes variableEncoding factorsEncoding)
    (fun r => (r.variables,r.factors)) (fun _ => rfl) (fun _ => rfl)

def duplicateComputes : Computes Raw.encoding Raw.encoding duplicate :=
  recode (pairComputes variablesComputes
    ((pairComputes factorsComputes factorsComputes).andThen
      (Holant.LocalDrafts.Tractability.AffineMachine.WireLists.append Raw.factorEncoding)))
    id (fun _ => rfl) (fun _ => rfl)

instance validDecidable (s : ℕ) (a : ℕ → ℕ) (r : Raw) : Decidable (Valid s a r) := by
  unfold Valid
  infer_instance

abbrev Input (s : ℕ) (a : ℕ → ℕ) := {r : Raw // Valid s a r}

def inputEncoding (s : ℕ) (a : ℕ → ℕ) : Encoding (Input s a) Bool where
  encode r := Raw.encoding.encode r.val
  decode bits := (Raw.encoding.decode bits).bind (fun r =>
    if h : Valid s a r then some ⟨r,h⟩ else none)
  decode_encode r := by simp [r.property]

def query {s : ℕ} {a : ℕ → ℕ} (r : Input s a) : Raw.Input s a := input r.val r.property

def queryComputes (s : ℕ) (a : ℕ → ℕ) :
    Computes (inputEncoding s a) (Raw.validatedEncoding s a) query :=
  recode duplicateComputes Subtype.val (fun _ => rfl) (fun _ => rfl)

variable {K : Type*} [CommSemiring K] {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (a i.val))

theorem query_value (r : Input s a) :
    Raw.value G (query r)=StableHigherCurrentOrdinarySquare.value (square G) r.val :=
  duplicate_typed_value G r.val r.property

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentOrdinarySquareProgramme
end
