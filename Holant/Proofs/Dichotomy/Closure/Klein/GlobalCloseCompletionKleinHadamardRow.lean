import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0XSource
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinDenseSeparated
import Holant.Proofs.Closure.ClosureSourceRows

/-! The actual standard-Klein Z representative supplies the literal scaled-X
row needed by the existing whole-family Hadamard native source. The original
representative scalar and its exact retained label are kept. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHadamardRow
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Holant.Marked
open Holant.Certificates.EqualityQuaternary
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
variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

abbrev retained := ClosureSourceRows.retainedPalette G P torsion q core literal (by decide : 2≤2)

def index := ClosureSourceRows.kleinIndex G P torsion .standard
  (GlobalCloseCompletionKleinDenseSeparated.coverage G P torsion cardinal noncyclic standard) 2

def key : completeGroup P.family torsion := (index G P torsion cardinal noncyclic standard).key

def multiplier : AlgebraicComplex := ClosureSourceRows.embedding G
  (index G P torsion cardinal noncyclic standard).coefficient/2

theorem multiplier_nonzero : multiplier G P torsion cardinal noncyclic standard≠0 :=
  div_ne_zero ((map_ne_zero _).mpr (index G P torsion cardinal noncyclic standard).nonzero) (by norm_num)

theorem key_mapped : transport W.basis
    ((actualRepresentative P.family torsion (key G P torsion cardinal noncyclic standard)).map (ClosureSourceRows.embedding G))=
      scale (multiplier G P torsion cardinal noncyclic standard) Signature.disequality := by
  have normal := (index G P torsion cardinal noncyclic standard).normal
  change ClosureSourceRows.representative G P torsion (key G P torsion cardinal noncyclic standard)=_ at normal
  change transport W.basis (ClosureSourceRows.representative G P torsion (key G P torsion cardinal noncyclic standard))=_
  rw [normal]
  funext b c
  cases b <;> cases c <;>
    simp [transport,W.basis,GlobalCloseCompletionA0Workfield.basis,
      ClosureMarkedDihedralA0.basis,ClosureMarkedCyclic.basis,basisA,UAInv,
      Kernel.mul_apply,Kernel.transpose,Klein.E,Klein.basisQ,Klein.matrix,scale,
      Signature.disequality,multiplier] <;> ring

def normalized : Signature (OI.K G) 2 :=
  Signature.coordinateAction (fun _ => W.inverse G)
    (Holant.Projective.BoundedTorsion.binarySignature
      (actualRepresentative P.family torsion (key G P torsion cardinal noncyclic standard)))

theorem normalized_value (x : Fin 2 → Bool) :
    ClosureSourceRows.embedding G (normalized G P torsion cardinal noncyclic standard x)=
      multiplier G P torsion cardinal noncyclic standard*Signature.disequality (x 0) (x 1) := by
  have hm : RingHomRealization.mapSignature (ClosureSourceRows.embedding G)
      (normalized G P torsion cardinal noncyclic standard)=W.basis.symm.action
        (kernelSignature ((actualRepresentative P.family torsion (key G P torsion cardinal noncyclic standard)).map
          (ClosureSourceRows.embedding G))) := by
    funext y
    simp only [normalized,RingHomRealization.mapSignature,Signature.coordinateAction,
      map_sum,map_mul,map_prod]
    simp_rw [show ClosureSourceRows.embedding G (W.inverse G _ _)=W.basis.inverse _ _ from W.inverse_value G _ _]
    rfl
  rw [transport_signature,key_mapped] at hm
  exact congrFun hm x

def coefficient : OI.K G := normalized G P torsion cardinal noncyclic standard (fun i => i.val=1)

theorem coefficient_value : ClosureSourceRows.embedding G (coefficient G P torsion cardinal noncyclic standard)=
    multiplier G P torsion cardinal noncyclic standard := by
  simpa [coefficient,Signature.disequality] using
    normalized_value G P torsion cardinal noncyclic standard (fun i => i.val=1)

theorem coefficient_nonzero : coefficient G P torsion cardinal noncyclic standard≠0 := by
  intro zero
  apply multiplier_nonzero G P torsion cardinal noncyclic standard
  exact (coefficient_value G P torsion cardinal noncyclic standard).symm.trans (by rw [zero,map_zero])

theorem normalized_literal : normalized G P torsion cardinal noncyclic standard=
    fun x => coefficient G P torsion cardinal noncyclic standard*Signature.disequality (x 0) (x 1) := by
  funext x
  apply (ClosureSourceRows.embedding G).injective
  rw [normalized_value,map_mul,coefficient_value]
  cases x 0 <;> cases x 1 <;> simp [Signature.disequality]

def label : Fin (retained G P torsion q core literal).count :=
  ClosureSourceRows.representativeLabel G P torsion q core literal (by decide : 2≤2) (key G P torsion cardinal noncyclic standard)

theorem retained_literal :
    (⟨(retained G P torsion q core literal).arity (label G P torsion cardinal noncyclic standard q core literal).val,
      (retained G P torsion q core literal).table (label G P torsion cardinal noncyclic standard q core literal)⟩ :
        AnySignature (OI.K G))=⟨2,Holant.Projective.BoundedTorsion.binarySignature
          (actualRepresentative P.family torsion (key G P torsion cardinal noncyclic standard))⟩ := by
  exact congrArg (fun u : TreeOccurrence (OI.K G) => u.1)
    (ClosureSourceRows.representative_saved G P torsion q core literal (by decide : 2≤2)
      (key G P torsion cardinal noncyclic standard))

theorem row_literal :
    (⟨(retained G P torsion q core literal).arity (label G P torsion cardinal noncyclic standard q core literal).val,
      W.table G (retained G P torsion q core literal) (label G P torsion cardinal noncyclic standard q core literal)⟩ :
        AnySignature (OI.K G))=⟨2,fun x =>
          coefficient G P torsion cardinal noncyclic standard*Signature.disequality (x 0) (x 1)⟩ := by
  rw [W.table_exact]
  have h := congrArg (fun f : AnySignature (OI.K G) =>
    (⟨f.1,Signature.coordinateAction (fun _ => W.inverse G) f.2⟩ : AnySignature (OI.K G)))
      (retained_literal G P torsion cardinal noncyclic standard q core literal)
  exact h.trans (congrArg (fun f : Signature (OI.K G) 2 => (⟨2,f⟩ : AnySignature (OI.K G)))
    (normalized_literal G P torsion cardinal noncyclic standard))

def row : GlobalCloseCompletionA0XSource.Row G (retained G P torsion q core literal) where
  label := label G P torsion cardinal noncyclic standard q core literal
  scalar := coefficient G P torsion cardinal noncyclic standard
  nonzero := coefficient_nonzero G P torsion cardinal noncyclic standard
  literal := row_literal G P torsion cardinal noncyclic standard q core literal


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHadamardRow
end
