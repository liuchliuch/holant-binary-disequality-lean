import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinOrdinaryExoticEq4
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0OrdinarySource
import Holant.Proofs.Dichotomy.Closure.Ordinary.GlobalCloseCompletionOrdinaryAnchorPins
import Holant.Proofs.Closure.ClosureSourceRowsKleinNative

/-! Actual current exotic q4 gives a finite ordinary scalar-Eq4 input over
the unchanged original coefficient field. All source labels and the complete
Hadamard source programme are retained before the two-pin construction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticOrdinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
namespace W
export GlobalCloseCompletionA0Workfield (field table table_value basis)
end W
namespace E
export GlobalCloseCompletionKleinOrdinaryExoticEq4 (graph graphLabels graph_exact graph_ordinary coefficient coefficient_nonzero graph_denote)
end E
namespace T
export GlobalCloseCompletionKleinOrdinaryHTransport (H zHalf)
end T
namespace A
export GlobalCloseCompletionKleinOrdinaryAttach (binary)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (exotic : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.exotic)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family) (literal : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev retained := ClosureSourceRows.retainedPalette G P torsion q core literal (by decide : 2≤2)
abbrev currentQ := RingHomRealization.mapSignature (ClosureSourceRows.embedding G) q
abbrev table := W.table G (retained G P torsion q core literal)
def mapped (i : Fin (retained G P torsion q core literal).count) :
    Signature AlgebraicComplex ((retained G P torsion q core literal).arity i.val) :=
  RingHomRealization.mapSignature (ClosureSourceRows.embedding G) (table G P torsion q core literal i)

def coverage : ClosureSourceRows.KleinCoverage G P torsion .exotic := by
  simpa only [exotic] using ClosureSourceRows.nativeKleinResources G P torsion cardinal noncyclic

def reps := ClosureSourceRows.kleinRepresentatives G P torsion .exotic q core literal
  (coverage G P torsion cardinal noncyclic exotic)

include stable in
theorem safe : Klein.PhysicalDeck (reps G P torsion cardinal noncyclic exotic q core literal) (currentQ G q) :=
  ClosureSourceRows.klein_sourceDeck G P torsion .exotic
    (coverage G P torsion cardinal noncyclic exotic) q core literal stable

theorem transformed_member (f : AnySignature AlgebraicComplex)
    (member : f∈ClosureSourceRows.ambientFamily G (retained G P torsion q core literal)) :
    ∃i : Fin (retained G P torsion q core literal).count,
      (⟨(retained G P torsion q core literal).arity i.val,mapped G P torsion q core literal i⟩ :
        AnySignature AlgebraicComplex)=⟨f.1,T.H.symm.action f.2⟩ := by
  obtain ⟨g,⟨i,rfl⟩,rfl⟩ := member
  refine ⟨i,?_⟩
  apply congrArg (fun f : Signature AlgebraicComplex _=>(⟨_,f⟩ : AnySignature AlgebraicComplex))
  exact funext (W.table_value G (retained G P torsion q core literal) i)

theorem q_exists : ∃i : Fin (retained G P torsion q core literal).count,
    (⟨(retained G P torsion q core literal).arity i.val,mapped G P torsion q core literal i⟩ :
      AnySignature AlgebraicComplex)=⟨4,T.H.symm.action (currentQ G q)⟩ :=
  transformed_member G P torsion q core literal _ (ClosureSourceRows.core_ambient_retained G P torsion q core literal)

def qLabel := (q_exists G P torsion q core literal).choose

theorem q_literal :
    (⟨(retained G P torsion q core literal).arity (qLabel G P torsion q core literal).val,
      mapped G P torsion q core literal (qLabel G P torsion q core literal)⟩ : AnySignature AlgebraicComplex)=
      ⟨4,T.H.symm.action (currentQ G q)⟩ := (q_exists G P torsion q core literal).choose_spec

theorem z_exists : ∃i : Fin (retained G P torsion q core literal).count,
    (⟨(retained G P torsion q core literal).arity i.val,mapped G P torsion q core literal i⟩ :
      AnySignature AlgebraicComplex)=⟨2,A.binary T.zHalf⟩ := by
  have mem : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
      ClosureSourceRows.ambientFamily G (retained G P torsion q core literal) := by
    refine ⟨⟨2,Holant.Projective.BoundedTorsion.binarySignature (X : Binary (K:=OI.K G))⟩,
      ClosureSourceRows.native_retained G P torsion q core literal (by decide : 2≤2),?_⟩
    apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
    funext x
    cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,
      Holant.Projective.BoundedTorsion.binarySignature,X,kernelSignature,Signature.disequality]
  obtain ⟨i,hi⟩ := transformed_member G P torsion q core literal _ mem
  refine ⟨i,hi.trans ?_⟩
  exact congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
    GlobalCloseCompletionKleinBAlgebra.H_X

def zLabel := (z_exists G P torsion q core literal).choose

theorem z_literal :
    (⟨(retained G P torsion q core literal).arity (zLabel G P torsion q core literal).val,
      mapped G P torsion q core literal (zLabel G P torsion q core literal)⟩ : AnySignature AlgebraicComplex)=
      ⟨2,A.binary T.zHalf⟩ := (z_exists G P torsion q core literal).choose_spec

theorem row_exists (k : Fin 4) : ∃i : Fin (retained G P torsion q core literal).count,
    (⟨(retained G P torsion q core literal).arity i.val,mapped G P torsion q core literal i⟩ :
      AnySignature AlgebraicComplex)=⟨2,A.binary (transport T.H
        ((reps G P torsion cardinal noncyclic exotic q core literal).matrix k))⟩ := by
  obtain ⟨i,hi⟩ := transformed_member G P torsion q core literal _
    (ClosureSourceRows.klein_retained G P torsion .exotic q core literal
      (coverage G P torsion cardinal noncyclic exotic) k)
  refine ⟨i,hi.trans ?_⟩
  exact congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
    (transport_signature T.H _)

def rowLabel (k : Fin 4) := (row_exists G P torsion cardinal noncyclic exotic q core literal k).choose

theorem row_literal (k : Fin 4) :
    (⟨(retained G P torsion q core literal).arity (rowLabel G P torsion cardinal noncyclic exotic q core literal k).val,
      mapped G P torsion q core literal (rowLabel G P torsion cardinal noncyclic exotic q core literal k)⟩ :
        AnySignature AlgebraicComplex)=⟨2,A.binary (transport T.H
          ((reps G P torsion cardinal noncyclic exotic q core literal).matrix k))⟩ :=
  (row_exists G P torsion cardinal noncyclic exotic q core literal k).choose_spec

abbrev initial := Network.corolla (T.H.symm.action (currentQ G q))
def initialLabels : Labelling (initial G q).shape
    (retained G P torsion q core literal).count 1 (retained G P torsion q core literal).arity where
  vertex _ := qLabel G P torsion q core literal
  vertex_arity _ := congrArg Sigma.fst (q_literal G P torsion q core literal)
  edge := Fin.elim0

abbrev graph := E.graph (reps G P torsion cardinal noncyclic exotic q core literal)
  (currentQ G q) (safe G P torsion cardinal noncyclic exotic q core literal stable) (initial G q)

def labels := E.graphLabels (reps G P torsion cardinal noncyclic exotic q core literal)
  (currentQ G q) (safe G P torsion cardinal noncyclic exotic q core literal stable)
  (mapped G P torsion q core literal) (zLabel G P torsion q core literal)
  (z_literal G P torsion q core literal) (rowLabel G P torsion cardinal noncyclic exotic q core literal)
  (row_literal G P torsion cardinal noncyclic exotic q core literal)
  (initial G q) (initialLabels G P torsion q core literal)

theorem graph_exact : LabelledNetwork.Exact (mapped G P torsion q core literal)
    (graph G P torsion cardinal noncyclic exotic q core literal stable)
    (labels G P torsion cardinal noncyclic exotic q core literal stable) :=
  E.graph_exact _ _ _ _ _ _ _ _ _ _ (fun _=>q_literal G P torsion q core literal)

theorem graph_ordinary : ∀e,(graph G P torsion cardinal noncyclic exotic q core literal stable).edge e=
    Signature.equality := E.graph_ordinary _ _ _ _ (fun e=>Fin.elim0 e)

abbrev outputScalar := E.coefficient (reps G P torsion cardinal noncyclic exotic q core literal)
  (currentQ G q) (safe G P torsion cardinal noncyclic exotic q core literal stable)

theorem outputScalar_nonzero : outputScalar G P torsion cardinal noncyclic exotic q core literal stable≠0 :=
  E.coefficient_nonzero _ _ (ClosureSourceRows.core_ambient_prime G P q core literal) _

theorem graph_denote : (graph G P torsion cardinal noncyclic exotic q core literal stable).denote=
    outputScalar G P torsion cardinal noncyclic exotic q core literal stable •
      Holant.EightVertex.ProductAnchor.equalityFour :=
  E.graph_denote _ _ _ _ (Network.denote_corolla _)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinExoticOrdinarySource
end
