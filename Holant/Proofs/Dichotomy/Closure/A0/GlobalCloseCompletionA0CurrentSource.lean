import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0NativeCodec
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Quaternary

/-! An actual finite native-X source containing every original current
Hadamard row and literal I. The complete source deck is retained before
normalization, and all reductions terminate at the original G oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CurrentSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Marked.SupportAtlas Holant.Certificates.EqualityQuaternary
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace W
export GlobalCloseCompletionA0Workfield (basis table table_value)
end W
namespace S
export GlobalCloseCompletionA0NativeSource (arity table old_signature identity_signature)
end S
namespace C
export GlobalCloseCompletionA0NativeCodec (mapped actualRow actualSource source macroFamily macroSource)
end C
namespace Q
export GlobalCloseCompletionA0Quaternary (normalized normalized_prime parity_and_complement)
end Q
namespace R
export GlobalCloseCompletionA0RetainedX (retained)
end R
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
variable (stable : ∀ f∈rawDeck P.family torsion q,MatchingOrZero (actualTransfers P.family) f)

abbrev retained := R.retained G P torsion q core literal
abbrev count := (retained G P torsion q core literal).count+1
abbrev arity := S.arity G (retained G P torsion q core literal)
abbrev mapped := C.mapped G (retained G P torsion q core literal)
abbrev source := C.actualSource G P torsion N q core literal

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (count G P torsion q core literal) =>
  (⟨arity G P torsion q core literal i.val,mapped G P torsion q core literal i⟩ : AnySignature AlgebraicComplex)

def oldLabel (i : Fin P.count) : Fin (count G P torsion q core literal) :=
  GlobalCloseCompletionA0XSource.oldLabel G (retained G P torsion q core literal)
    (RetainedCatalogue.oldLabel G P torsion q i)

theorem old_mapped (i : Fin P.count) :
    (⟨arity G P torsion q core literal (oldLabel G P torsion q core literal i).val,
      mapped G P torsion q core literal (oldLabel G P torsion q core literal i)⟩ :
        AnySignature AlgebraicComplex)=
      ⟨P.arity i.val,W.basis.symm.action (StableHigherCurrentPurePinsCore.mapped G P i)⟩ := by
  have ht := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G))
    (S.old_signature G (retained G P torsion q core literal) (RetainedCatalogue.oldLabel G P torsion q i))
  refine ht.trans ?_
  have hv : RingHomRealization.mapAny (ClosureSourceRows.embedding G)
      ⟨(retained G P torsion q core literal).arity (RetainedCatalogue.oldLabel G P torsion q i).val,
        W.table G (retained G P torsion q core literal) (RetainedCatalogue.oldLabel G P torsion q i)⟩=
      (⟨(retained G P torsion q core literal).arity (RetainedCatalogue.oldLabel G P torsion q i).val,
        W.basis.symm.action (StableHigherCurrentPurePinsCore.mapped G (retained G P torsion q core literal)
          (RetainedCatalogue.oldLabel G P torsion q i))⟩ : AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex _ => (⟨_,f⟩ : AnySignature AlgebraicComplex))
    exact funext (W.table_value G (retained G P torsion q core literal) (RetainedCatalogue.oldLabel G P torsion q i))
  refine hv.trans ?_
  exact congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,W.basis.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)⟩ :
      AnySignature AlgebraicComplex))
        (congrArg (fun u : TreeOccurrence (OI.K G) => u.1) (RetainedCatalogue.old_saved G P torsion q i))

theorem normalized_member : (⟨4,Q.normalized G q⟩ : AnySignature AlgebraicComplex)∈
    family G P torsion q core literal := by
  obtain ⟨j,hj⟩ := core.retained
  have hq : (⟨P.arity j.val,P.table j⟩ : AnySignature (OI.K G))=⟨4,q⟩ := hj.trans literal
  refine ⟨oldLabel G P torsion q core literal j,(old_mapped G P torsion q core literal j).trans ?_⟩
  exact congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,W.basis.symm.action (RingHomRealization.mapSignature (ClosureSourceRows.embedding G) f.2)⟩ :
      AnySignature AlgebraicComplex)) hq

def identityLabel : Fin (count G P torsion q core literal) :=
  GlobalCloseCompletionA0XSource.xLabel G (retained G P torsion q core literal)

theorem identity_literal :
    (⟨arity G P torsion q core literal (identityLabel G P torsion q core literal).val,
      mapped G P torsion q core literal (identityLabel G P torsion q core literal)⟩ :
        AnySignature AlgebraicComplex)=⟨2,kernelSignature Signature.equality⟩ := by
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G))
    (S.identity_signature G (retained G P torsion q core literal))
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality]

theorem identity_member : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈
    family G P torsion q core literal :=
  ⟨identityLabel G P torsion q core literal,identity_literal G P torsion q core literal⟩

theorem flip_realizes (mask : Word) :
    Gadget.Realizes (family G P torsion q core literal) .disequality (Flip.value (Q.normalized G q) mask) :=
  Flip.actual _ _ (Gadget.realizes_of_mem _ .disequality _ (normalized_member G P torsion q core literal))
    (Gadget.realizes_of_mem _ .disequality _ (identity_member G P torsion q core literal)) mask

def FullParity (p : Bool) : Prop := ∀x,Q.normalized G q x≠0 ↔ parity x=p

structure SparseOutput : Type 1 where
  mask : Word
  missing : Q.normalized G q mask=0
  paritySupported : ∀x,Q.normalized G q x≠0 → parity x=parity mask
  eo : DenseEOUnitLocal.EOSupport (Flip.value (Q.normalized G q) mask)
  prime : TensorPrime (Flip.value (Q.normalized G q) mask)
  actual : Gadget.Realizes (family G P torsion q core literal) .disequality (Flip.value (Q.normalized G q) mask)
  oneOriginal : (Finset.univ.filter (fun v : Fin (Flip.network (Q.normalized G q) mask).shape.vertices =>
    (Flip.network (Q.normalized G q) mask).shape.arity v=4)).card=1

include N stable in
theorem sparse_or_full : (∃p,FullParity G q p) ∨ Nonempty (SparseOutput G P torsion q core literal) := by
  classical
  obtain ⟨p,supported,closed⟩ := Q.parity_and_complement G P torsion N q core literal stable
  by_cases full : FullParity G q p
  · exact Or.inl ⟨p,full⟩
  · right
    have missing : ∃mask : Word,parity mask=p ∧ Q.normalized G q mask=0 := by
      by_contra h
      push Not at h
      apply full
      intro x
      exact ⟨supported x,fun hx => h x hx⟩
    obtain ⟨mask,hp,hzero⟩ := missing
    have same : ∀x,Q.normalized G q x≠0 → parity x=parity mask := fun x hx => (supported x hx).trans hp.symm
    exact ⟨⟨mask,hzero,same,
      StableCurrentEvenEOTransport.eo_of_missing_parity_word _ mask same hzero ((closed mask).mpr hzero),
      flip_prime (Q.normalized_prime G P q core literal) mask,flip_realizes G P torsion q core literal mask,
      Flip.quaternary_count _ _⟩⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0CurrentSource
end
