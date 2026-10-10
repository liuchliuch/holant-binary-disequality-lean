import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionPinNative
import Holant.Proofs.Hardness.GeneralEOPairedCSPOriginalField
import Holant.Proofs.Reductions.CanonicalFamily.Semantics

/-! Finite duplicate labels are removed by the actual accepted row recoder.
The coefficient field and its coordinate encoding are fixed throughout. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyDuplicate
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity BinaryCompose
namespace R
export Holant.LocalDrafts.Hardness.CanonicalFamily.Relabel
  (input computes raw row label ordered_ports)
end R
namespace C
export UniversalPairReduction.Surgery.Choice (table evaluate denote_eq_evaluate)
end C
namespace N
export GeneralEOPairedCSPNative (targetValue tables target_semantics)
end N
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

variable {K : Type} [Field K] [Algebra ℚ K] {d s t : ℕ} {arity : ℕ → ℕ}
variable (F : FixedField K d) (G : (i : Fin s) → Signature K (arity i.val))
variable (label : Fin t → Fin s)

def arities (k : ℕ) : ℕ := if h : k<t then arity (label ⟨k,h⟩).val else 0

@[simp] theorem arity_label (i : Fin t) : arities (arity:=arity) label i.val=arity (label i).val := by
  simp [arities,i.isLt]

def signatures (i : Fin t) : Signature K (arities (arity:=arity) label i.val) :=
  fun x => G (label i) (fun k => x (Fin.cast (arity_label label i).symm k))

def query : ExactSignatureTables.Input t 1 (arities (arity:=arity) label) →
    ExactSignatureTables.Input s 1 arity := R.input label (fun i => (arity_label label i).symm)

def queryComputes : Computes (RawClosedNetwork.validatedEncoding t 1 (arities (arity:=arity) label))
    (RawClosedNetwork.validatedEncoding s 1 arity) (query (arity:=arity) label) :=
  R.computes label (fun i => (arity_label label i).symm)

omit [Algebra ℚ K] in
theorem table_label (i : Fin t) (bits : List Bool) :
    C.table (signatures G label) i.val bits=C.table G (label i).val bits := by
  simp only [C.table,dite_eq_left i.isLt,dite_eq_left (label i).isLt,signatures]
  rfl

theorem query_value (r : ExactSignatureTables.Input t 1 (arities (arity:=arity) label)) :
    N.targetValue F (signatures G label) r=N.targetValue F G (query label r) := by
  rw [N.target_semantics,N.target_semantics,C.denote_eq_evaluate,C.denote_eq_evaluate]
  have h := Holant.LocalDrafts.Hardness.CanonicalFamily.Relabel.value_scaled label
    (C.table (signatures G label)) (C.table G) (fun _ => (1:K))
    (fun i => (arity_label label i).symm) r (fun i bits => by simpa using table_label G label i bits)
  have hp : Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
      (fun _ : Fin t => (1:K)) r.val=1 := by
    unfold Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.value
    apply List.prod_eq_one
    intro z hz
    obtain ⟨row,hrow,rfl⟩ := List.mem_map.mp hz
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hrow
    simp only [Holant.LocalDrafts.Hardness.RootPreprocessing.OccurrenceProduct.total,
      dite_eq_left (r.property.1 i).1]
  simpa only [hp,one_mul,query] using h

/-- A physical one-query reduction, preserving every ordered port and edge. -/
def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (arities (arity:=arity) label)) F.encoding
    (RawClosedNetwork.validatedEncoding s 1 arity) F.encoding
    (N.targetValue F (signatures G label)) (N.targetValue F G) :=
  Holant.LocalDrafts.MainChain.controlledOneQueryOfEq (queryComputes label)
    (identityComputes F.encoding) ((N.tables F G).outputBound F)
    (N.targetValue F (signatures G label)) (query_value F G label)

theorem query_ports (r : ExactSignatureTables.Input t 1 (arities (arity:=arity) label)) :
    (query label r).val.vertices.map Prod.snd=r.val.vertices.map Prod.snd :=
  R.ordered_ports label r.val

theorem query_edges (r : ExactSignatureTables.Input t 1 (arities (arity:=arity) label)) :
    (query label r).val.edges=r.val.edges := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyDuplicate
