import Holant.Proofs.Traversal.LocalAffineSupport.Bounds
import Holant.Proofs.Traversal.LocalAffineSupport.Boundary


namespace Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface
open Holant Holant.Tractable AffinePhase Holant.Complexity Computability
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section

variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)
abbrev Input := RawRows.Input (s:=s) (b:=b) (arity:=arity)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding s b arity
abbrev value := Matrix.value D
abbrev computes := Matrix.computes D

theorem specification (r : Input (s:=s) (b:=b) (arity:=arity)) :
    (value D r).1 = 2*r.val.edges.length ∧ Codec.Rectangular (value D r) ∧
      ∀ x : Word (2*r.val.edges.length),
        (Codec.support (value D r)).Holds x ↔
          (LocalAffineLabels.network D r).assignmentTerm Fin.elim0
            (Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment r.val.edges.length x) ≠ 0 :=
  ⟨rfl, Matrix.value_rectangular D r, Correctness.support_iff D r⟩

theorem same_holds_global (r : Input (s:=s) (b:=b) (arity:=arity))
    (x : Word (2*r.val.edges.length)) :
    (Codec.support (value D r)).Holds x ↔
      (Holant.LocalDrafts.MainChain.LocalAffineSupport.global (LocalAffineLabels.network D r)
        (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
        (fun e => D.edgeLocal (r.val.edgeLabel r.property e))).Holds x :=
  Correctness.same_holds_global D r x

/-- A physical Boolean word is interpreted in the same default-false convention
as the delivered matrix codec. For exact-length solver output no padding occurs. -/
def word (r : Input (s:=s) (b:=b) (arity:=arity)) (bits : List Bool) : Word (2*r.val.edges.length) :=
  fun j => bits.getD j.val false

theorem decoded_word_support (r : Input (s:=s) (b:=b) (arity:=arity)) (bits : List Bool) :
    (Codec.support (value D r)).Holds (word r bits) ↔
      (LocalAffineLabels.network D r).assignmentTerm Fin.elim0
        (Holant.LocalDrafts.MainChain.LocalAffineSupport.assignment r.val.edges.length (word r bits)) ≠ 0 :=
  Correctness.support_iff D r (word r bits)

theorem output_roundtrip (r : Input (s:=s) (b:=b) (arity:=arity)) :
    Codec.encoding.decode (Codec.encoding.encode (value D r)) = some (value D r) :=
  Codec.faithful _

theorem inFP : InFP (inputEncoding (s:=s) (b:=b) (arity:=arity)) Codec.encoding (value D) :=
  Matrix.inFP D

end
end Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface
