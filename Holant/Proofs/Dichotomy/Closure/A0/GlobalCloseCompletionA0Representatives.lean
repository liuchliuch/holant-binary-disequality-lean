import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0CurrentSource
import Holant.Certificates.EqualityQuaternary.MonomialDeck

/-! Every standard root-phase binary in the normalized A0 native alphabet
has an actual original complete-group key and a retained full-deck label.
The ambient projective multipliers are retained literally; no coordinate
matrix is introduced as an assumed source resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Representatives
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionA0CurrentSource (retained family)
end C
namespace W
export GlobalCloseCompletionA0Workfield (basis table table_value)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

abbrev selection (p : Bool) (t : Phase N.selected.m) :=
  ClosureMarkedDihedralA0.Source.standard_source_representative
    (ClosureSourceRows.embedding G) P.family torsion N p t.val t.property

def key (p : Bool) (t : Phase N.selected.m) : completeGroup P.family torsion :=
  (selection G P torsion N p t).choose

def multiplier (p : Bool) (t : Phase N.selected.m) : Scalar :=
  (selection G P torsion N p t).choose_spec.choose

def matrix (p : Bool) (t : Phase N.selected.m) : Mat :=
  transport W.basis ((actualRepresentative P.family torsion (key G P torsion N p t)).map
    (ClosureSourceRows.embedding G))

theorem normal_form (p : Bool) (t : Phase N.selected.m) :
    matrix G P torsion N p t=scale (multiplier G P torsion N p t) (standard p t.val) :=
  (selection G P torsion N p t).choose_spec.choose_spec.2

theorem member (p : Bool) (t : Phase N.selected.m) :
    (⟨2,kernelSignature (matrix G P torsion N p t)⟩ : AnySignature AlgebraicComplex)∈
      C.family G P torsion q core literal := by
  let j := ClosureSourceRows.representativeLabel G P torsion q core literal (by decide : 2≤2)
    (key G P torsion N p t)
  have hj : (⟨(C.retained G P torsion q core literal).arity j.val,
      (C.retained G P torsion q core literal).table j⟩ : AnySignature (OI.K G))=
        ⟨2,Holant.Projective.BoundedTorsion.binarySignature
          (actualRepresentative P.family torsion (key G P torsion N p t))⟩ :=
    congrArg (fun u : TreeOccurrence (OI.K G) => u.1)
      (ClosureSourceRows.representative_saved G P torsion q core literal (by decide : 2≤2)
        (key G P torsion N p t))
  refine ⟨GlobalCloseCompletionA0XSource.oldLabel G (C.retained G P torsion q core literal) j,?_⟩
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G))
    (GlobalCloseCompletionA0NativeSource.old_signature G (C.retained G P torsion q core literal) j)
  refine h.trans ?_
  have hv : RingHomRealization.mapAny (ClosureSourceRows.embedding G)
      ⟨(C.retained G P torsion q core literal).arity j.val,
        W.table G (C.retained G P torsion q core literal) j⟩=
      (⟨(C.retained G P torsion q core literal).arity j.val,
        W.basis.symm.action (StableHigherCurrentPurePinsCore.mapped G (C.retained G P torsion q core literal) j)⟩ :
          AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex _ => (⟨_,f⟩ : AnySignature AlgebraicComplex))
    exact funext (W.table_value G (C.retained G P torsion q core literal) j)
  refine hv.trans ?_
  have hh := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,W.basis.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)⟩ :
      AnySignature AlgebraicComplex)) hj
  refine hh.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  have mapped : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (Holant.Projective.BoundedTorsion.binarySignature
        (actualRepresentative P.family torsion (key G P torsion N p t)))=
      kernelSignature ((actualRepresentative P.family torsion (key G P torsion N p t)).map
        (ClosureSourceRows.embedding G)) := rfl
  rw [mapped]
  exact transport_signature W.basis _

def produce : MonomialRepresentatives (C.family G P torsion q core literal) N.selected.m where
  matrix := matrix G P torsion N
  multiplier := multiplier G P torsion N
  multiplier_ne_zero p t := (selection G P torsion N p t).choose_spec.choose_spec.1
  actual p t := Gadget.realizes_of_mem _ .disequality _ (member G P torsion N q core literal p t)
  normal_form := normal_form G P torsion N

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Representatives
end
