import Holant.Proofs.Traversal.LocalAffineSupport.Interface
import Holant.Proofs.BinaryInterpolation.FiniteSupportMachine.Source
import Holant.Proofs.Algorithms.OriginalFamily


namespace Holant.LocalDrafts.MainChain.LocalAffineEncodedReference
open Computability Holant.Tractable Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.BinaryInterpolation.FiniteSupportMachine
noncomputable section
variable {s b : ℕ} {arity : ℕ → ℕ} (D : LocalAffineLabels.Family s b arity)

abbrev Input := ExactSignatureTables.Input s b arity

def value (r : Input (s:=s) (b:=b) (arity:=arity)) : Option (List Bool) :=
  Semantics.solve (Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface.value D r)

def computes : Computes (RawClosedNetwork.validatedEncoding s b arity)
    Controller.outputEncoding (value D) :=
  (Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface.computes D).andThen Source.computes

def assignment (r : Input (s:=s) (b:=b) (arity:=arity)) (w : List Bool) :
    (Fin r.val.edges.length × Bool) → Bool :=
  LocalAffineSupport.assignment r.val.edges.length
    (Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface.word r w)

theorem some_length (r : Input (s:=s) (b:=b) (arity:=arity)) (w : List Bool)
    (h : value D r=some w) : w.length=2*r.val.edges.length :=
  (Source.sound _ w h).1

theorem some_supported (r : Input (s:=s) (b:=b) (arity:=arity)) (w : List Bool)
    (h : value D r=some w) :
    (LocalAffineLabels.network D r).assignmentTerm Fin.elim0 (assignment r w) ≠ 0 := by
  have hs := (Source.sound _ w h).2
  exact (Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface.decoded_word_support
    D r w).mp hs

theorem none_zero (r : Input (s:=s) (b:=b) (arity:=arity)) (h : value D r=none) :
    (LocalAffineLabels.network D r).denote Fin.elim0=0 := by
  have hn := (Source.none_iff _).mp h
  apply LocalAffineSupport.denote_zero_of_unsatisfiable (LocalAffineLabels.network D r)
    (fun v => D.vertexLocal (r.val.signatureLabel r.property v))
    (fun e => D.edgeLocal (r.val.edgeLabel r.property e))
  rintro ⟨x,hx⟩
  exact hn ⟨x,(Holant.LocalDrafts.TraversalCompletion.LocalAffineSupport.Interface.same_holds_global
    D r x).mpr hx⟩

theorem none_original_zero (r : Input (s:=s) (b:=b) (arity:=arity)) (h : value D r=none) :
    OriginalFamily.value D.signatures D.kernels r=0 := by
  apply Subtype.ext
  rw [OriginalFamily.value_exact]
  exact none_zero D r h

theorem some_labelled_value (r : Input (s:=s) (b:=b) (arity:=arity)) (w : List Bool)
    (h : value D r=some w) :
    (LocalAffineLabels.labelled D r (assignment r w)).denote Fin.elim0=
      (LocalAffineLabels.network D r).denote Fin.elim0 := by
  rw [LocalAffineLabels.labelled_eq_gauged D r _ (some_supported D r w h)]
  exact LocalAffineNetwork.denote_gauged _ _

theorem primitive_bound (r : Input (s:=s) (b:=b) (arity:=arity)) :
    primitiveCost (computes D).machine ((computes D).outputs r).steps
      (some (Turing.initList (computes D).machine.computer
        ((RawClosedNetwork.validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes D)).eval
        ((RawClosedNetwork.validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes D) r

end
end Holant.LocalDrafts.MainChain.LocalAffineEncodedReference
