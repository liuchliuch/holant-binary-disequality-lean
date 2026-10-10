import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0Workfield
import Holant.Proofs.Closure.ClosureSourceRows

/-! A literal original-field normalized X row from an actual complete-group
representative. The full original deck is retained with its existing source
programme before coordinates are changed. No coordinate mark is installed as
a gadget, and the nonzero multiplier is a real original-field table entry. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RetainedX
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace W
export GlobalCloseCompletionA0Workfield (K inverse basis table table_exact inverse_value)
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

abbrev retained := ClosureSourceRows.retainedPalette G P torsion q core literal (by decide : 2≤2)

def key : completeGroup P.family torsion :=
  (ClosureMarkedDihedralA0.Source.standard_source_representative
    (ClosureSourceRows.embedding G) P.family torsion N true 1 (by simp [Roots])).choose

def multiplier : AlgebraicComplex :=
  (ClosureMarkedDihedralA0.Source.standard_source_representative
    (ClosureSourceRows.embedding G) P.family torsion N true 1 (by simp [Roots])).choose_spec.choose

theorem multiplier_nonzero : multiplier G P torsion N≠0 :=
  (ClosureMarkedDihedralA0.Source.standard_source_representative
    (ClosureSourceRows.embedding G) P.family torsion N true 1 (by simp [Roots])).choose_spec.choose_spec.1

theorem key_mapped : transport W.basis
    ((actualRepresentative P.family torsion (key G P torsion N)).map (ClosureSourceRows.embedding G))=
      scale (multiplier G P torsion N) Signature.disequality := by
  have h := (ClosureMarkedDihedralA0.Source.standard_source_representative
    (ClosureSourceRows.embedding G) P.family torsion N true 1 (by simp [Roots])).choose_spec.choose_spec.2
  have standard : ClosureMarkedDihedral.standard true 1=Signature.disequality := by
    funext b c
    cases b <;> cases c <;>
      simp [ClosureMarkedDihedral.standard,S,R,Kernel.mul_apply,diagonalKernel,Signature.disequality]
  exact h.trans (congrArg (scale (multiplier G P torsion N)) standard)

def normalized : Signature (OI.K G) 2 :=
  Signature.coordinateAction (fun _ => W.inverse G)
    (Holant.Projective.BoundedTorsion.binarySignature
      (actualRepresentative P.family torsion (key G P torsion N)))

theorem normalized_value (x : Fin 2 → Bool) :
    ClosureSourceRows.embedding G (normalized G P torsion N x)=
      multiplier G P torsion N*Signature.disequality (x 0) (x 1) := by
  have hm : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (normalized G P torsion N)=W.basis.symm.action
        (kernelSignature ((actualRepresentative P.family torsion (key G P torsion N)).map
          (ClosureSourceRows.embedding G))) := by
    funext y
    simp only [normalized,RingHomRealization.mapSignature,Signature.coordinateAction,
      map_sum,map_mul,map_prod]
    simp_rw [show ClosureSourceRows.embedding G (W.inverse G _ _)=W.basis.inverse _ _ from W.inverse_value G _ _]
    rfl
  rw [transport_signature,key_mapped] at hm
  exact congrFun hm x

def coefficient : OI.K G := normalized G P torsion N (fun i => i.val=1)

theorem coefficient_value : ClosureSourceRows.embedding G (coefficient G P torsion N)=
    multiplier G P torsion N := by
  simpa [coefficient,Signature.disequality] using
    normalized_value G P torsion N (fun i => i.val=1)

theorem coefficient_nonzero : coefficient G P torsion N≠0 := by
  intro zero
  apply multiplier_nonzero G P torsion N
  exact (coefficient_value G P torsion N).symm.trans (by rw [zero,map_zero])

theorem normalized_literal : normalized G P torsion N=
    fun x => coefficient G P torsion N*Signature.disequality (x 0) (x 1) := by
  funext x
  apply (ClosureSourceRows.embedding G).injective
  rw [normalized_value,map_mul,coefficient_value]
  cases x 0 <;> cases x 1 <;> simp [Signature.disequality]

def label : Fin (retained G P torsion q core literal).count :=
  ClosureSourceRows.representativeLabel G P torsion q core literal (by decide : 2≤2) (key G P torsion N)

theorem retained_literal :
    (⟨(retained G P torsion q core literal).arity (label G P torsion N q core literal).val,
      (retained G P torsion q core literal).table (label G P torsion N q core literal)⟩ :
        AnySignature (OI.K G))=⟨2,Holant.Projective.BoundedTorsion.binarySignature
          (actualRepresentative P.family torsion (key G P torsion N))⟩ := by
  exact congrArg (fun u : TreeOccurrence (OI.K G) => u.1)
    (ClosureSourceRows.representative_saved G P torsion q core literal (by decide : 2≤2)
      (key G P torsion N))

theorem row_literal :
    (⟨(retained G P torsion q core literal).arity (label G P torsion N q core literal).val,
      W.table G (retained G P torsion q core literal) (label G P torsion N q core literal)⟩ :
        AnySignature (OI.K G))=⟨2,fun x =>
          coefficient G P torsion N*Signature.disequality (x 0) (x 1)⟩ := by
  rw [W.table_exact]
  have h := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,Signature.coordinateAction (fun _ => W.inverse G) f.2⟩ : AnySignature (OI.K G)))
      (retained_literal G P torsion N q core literal)
  exact h.trans (congrArg (fun f : Signature (OI.K G) 2 => (⟨2,f⟩ : AnySignature (OI.K G)))
    (normalized_literal G P torsion N))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0RetainedX
end
