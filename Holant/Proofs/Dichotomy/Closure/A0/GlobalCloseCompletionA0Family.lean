import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0NativeCodec
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Classification

/-! Exact set-level description of the same finite native-X source table:
every old Hadamard row, plus literal I. The finite dictionary is never treated
as a saturation palette. Positivity/nonzero follow from the actual old palette. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Family
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (basis mapped table_value)
end W
namespace S
export GlobalCloseCompletionA0NativeSource (arity table old_signature identity_signature)
end S
namespace C
export GlobalCloseCompletionA0NativeCodec (mapped)
end C
namespace L
export GlobalCloseCompletionA0XSource (oldLabel xLabel)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

def family : SignatureFamily AlgebraicComplex :=
  familyAction W.basis.symm (ClosureSourceRows.ambientFamily G P) ∪
    {(⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)}
abbrev finiteFamily := UniversalPairReduction.FiniteFamily.family (C.mapped G P)

theorem identity : RetainsIdentity (family G P) := Or.inr rfl

theorem old_mapped (i : Fin P.count) :
    (⟨S.arity G P (L.oldLabel G P i).val,C.mapped G P (L.oldLabel G P i)⟩ : AnySignature AlgebraicComplex)=
      ⟨P.arity i.val,W.basis.symm.action (W.mapped G P i)⟩ := by
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G)) (S.old_signature G P i)
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex (P.arity i.val) => (⟨P.arity i.val,f⟩ : AnySignature AlgebraicComplex))
  exact funext (W.table_value G P i)

theorem identity_literal :
    (⟨S.arity G P (L.xLabel G P).val,C.mapped G P (L.xLabel G P)⟩ : AnySignature AlgebraicComplex)=
      ⟨2,kernelSignature Signature.equality⟩ := by
  have h := congrArg (RingHomRealization.mapAny (ClosureSourceRows.embedding G)) (S.identity_signature G P)
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.equality]

theorem family_eq : family G P=finiteFamily G P := by
  ext f
  constructor
  · rintro (⟨_,⟨_,⟨i,rfl⟩,rfl⟩,rfl⟩|rfl)
    · exact ⟨L.oldLabel G P i,old_mapped G P i⟩
    · exact ⟨L.xLabel G P,identity_literal G P⟩
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<P.count
    · have label : i=L.oldLabel G P ⟨i.val,hi⟩ := Fin.ext rfl
      rw [label]
      have member : (⟨P.arity i.val,W.basis.symm.action (W.mapped G P ⟨i.val,hi⟩)⟩ :
          AnySignature AlgebraicComplex)∈family G P :=
        Or.inl ⟨_,⟨⟨P.arity i.val,P.table ⟨i.val,hi⟩⟩,⟨⟨i.val,hi⟩,rfl⟩,rfl⟩,rfl⟩
      exact Eq.mpr (congrArg (fun f : AnySignature AlgebraicComplex=>f∈family G P)
        (old_mapped G P ⟨i.val,hi⟩)) member
    · have label : i=L.xLabel G P := Fin.ext (by change i.val=P.count; have := i.isLt; omega)
      rw [label]
      have h := identity_literal G P
      exact Eq.mpr (congrArg (fun f : AnySignature AlgebraicComplex=>f∈family G P) h) (identity G P)

theorem preprocessed : Preprocessed (family G P) := by
  rintro f (old|rfl)
  · exact Conformal.preprocessed_familyAction W.basis.symm
      (GlobalCloseCompletionEq4Classification.current_preprocessed G P) f old
  · refine ⟨by decide,?_⟩
    intro zero
    have h := congrFun zero ![false,false]
    simp [kernelSignature,Signature.equality] at h

theorem finite_preprocessed : Preprocessed (finiteFamily G P) := by
  rw [←family_eq]
  exact preprocessed G P


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0Family
end
