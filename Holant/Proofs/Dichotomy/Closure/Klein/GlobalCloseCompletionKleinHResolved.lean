import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHadamardRow
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinFiniteEq4
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinBAlgebra
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0DenseCanonical
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0OpenCoordinate

/-! Standard-Klein actual Z supplies the existing Hadamard finite native
source. Its actual native-X row gives the normalized Z correction, allowing
arbitrary original current gadgets to be transported, with all scalars kept. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHResolved
open Holant Holant.Tractable Holant.Algebraic Holant.Marked
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Projective.BoundedTorsion hiding binarySignature
open Holant.Certificates.MatchingContractionClosure
namespace C
export GlobalCloseCompletionA0CurrentSource (family retained count arity mapped identity_member)
end C
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (Z normal)
end T
namespace W
export GlobalCloseCompletionA0Workfield (basis)
end W
namespace F
export GlobalCloseCompletionKleinFiniteEq4 (Input classified)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (torsion : ResidualTorsion P.family)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

private def gate : Matrix Bool Bool AlgebraicComplex := Matrix.of (fun b c=>(1/2)*T.Z b c)

include core literal in
theorem gate_actual : Gadget.Realizes (C.family G P torsion q core literal) .disequality
    (binarySignature gate) := by
  have member := GlobalCloseCompletionA0CurrentNativeRow.member G P torsion q core literal
  have value : W.basis.symm.action (kernelSignature Signature.disequality)=
      binarySignature gate := GlobalCloseCompletionKleinBAlgebra.H_X
  rw [value] at member
  exact Gadget.realizes_of_mem _ .disequality _ member

private theorem inverse_edge : Kernel.pullback Signature.disequality W.basis.matrix=
    scale (-4) (GlobalCloseCompletionA0KernelRealizes.edge gate) := by
  funext b c
  cases b <;> cases c <;>
    norm_num [W.basis,GlobalCloseCompletionA0Workfield.basis,ClosureMarkedDihedralA0.basis,
      ClosureMarkedCyclic.basis,basisA,UA,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,
      GlobalCloseCompletionA0KernelRealizes.edge,gate,T.Z,X,Matrix.mul_apply,scale,Signature.disequality]

include core literal in
theorem forward {n : ℕ} (f : Signature AlgebraicComplex n)
    (actual : Gadget.Realizes (ClosureSourceRows.ambientFamily G P) .disequality f) :
    Gadget.RealizesUpTo (C.family G P torsion q core literal) .disequality (W.basis.symm.action f) := by
  apply GlobalCloseCompletionA0OpenCoordinate.coordinate (C.family G P torsion q core literal)
    (C.identity_member G P torsion q core literal) gate (gate_actual G P torsion q core literal)
    W.basis.symm (-4) (by norm_num) inverse_edge (ClosureSourceRows.ambientFamily G P)
    (StableDenseGaugeCurrent.ambient_identity G P) ?_ f actual
  intro g hg
  refine ⟨1,one_ne_zero,?_⟩
  simpa only [one_mul] using (Gadget.realizes_of_mem _ .disequality _
    (GlobalCloseCompletionA0DenseCanonical.normalized_included G P torsion q core literal ⟨g,hg,rfl⟩))

include core literal in
theorem forward_upTo {n : ℕ} (f : Signature AlgebraicComplex n)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality f) :
    Gadget.RealizesUpTo (C.family G P torsion q core literal) .disequality (W.basis.symm.action f) := by
  obtain ⟨c,hc,actual⟩ := actual
  have ha := forward G P torsion q core literal _ actual
  have linear : W.basis.symm.action (fun x=>c*f x)=fun x=>c*W.basis.symm.action f x := by
    funext x
    simp only [InvertibleKernel.action,Signature.coordinateAction,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro y _
    ring
  rw [linear] at ha
  obtain ⟨d,hd,ha⟩ := ha
  refine ⟨d*c,mul_ne_zero hd hc,?_⟩
  convert ha using 1
  funext x
  ring

variable (cardinal : Nat.card (completeGroup P.family torsion)=4)
variable (noncyclic : ¬IsCyclic (completeGroup P.family torsion))
variable (standard : ClosureSourceRows.nativeKleinKind G P torsion cardinal noncyclic=.standard)

def input : F.Input G where
  count := C.count G P torsion q core literal
  arity := C.arity G P torsion q core literal
  table := C.mapped G P torsion q core literal
  identity := C.identity_member G P torsion q core literal
  source := GlobalCloseCompletionA0NativeCodec.source G (C.retained G P torsion q core literal)
    (GlobalCloseCompletionKleinHadamardRow.row G P torsion cardinal noncyclic standard q core literal)

include cardinal noncyclic standard core literal in
theorem eq4_classified (actual : Gadget.RealizesUpTo (C.family G P torsion q core literal)
    .disequality (Holant.EightVertex.ProductAnchor.equalityFour (K:=AlgebraicComplex))) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  rcases F.classified G (input G P torsion q core literal cardinal noncyclic standard)
    (GlobalCloseCompletionA0DenseCanonical.preprocessed G P torsion q core literal) actual with
      (affine|product|localAffine)|hard
  · exact Or.inl (ClosureNativePresentation.tractX_forward_affine
      (GlobalCloseCompletionA0DenseCanonical.common G P torsion q core literal .affine affine))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_product
      (GlobalCloseCompletionA0DenseCanonical.common G P torsion q core literal .product product))
  · exact Or.inl (ClosureNativePresentation.tractX_forward_localAffine
      (GlobalCloseCompletionA0DenseCanonical.common G P torsion q core literal .localAffine localAffine))
  · exact Or.inr hard

include cardinal noncyclic standard core literal in
theorem classified (f : Signature AlgebraicComplex 4)
    (actual : Gadget.RealizesUpTo (ClosureSourceRows.ambientFamily G P) .disequality f)
    (a b c d : AlgebraicComplex) (form : W.basis.symm.action f=T.normal a b c d)
    (separated : (a^2-b^2)^2≠(c^2-d^2)^2) :
    GlobalCloseCompletionKleinEq4Source.CurrentTract G P ∨ GlobalCloseCompletionKleinEq4Source.Hard G := by
  have z : Gadget.RealizesUpTo (C.family G P torsion q core literal) .disequality
      (fun x : Fin 2→Bool=>T.Z (x 0) (x 1)) :=
    ⟨1/2,by norm_num,gate_actual G P torsion q core literal⟩
  have hq := forward_upTo G P torsion q core literal f actual
  rw [form] at hq
  exact eq4_classified G P torsion q core literal cardinal noncyclic standard
    (GlobalCloseCompletionKleinTwistedActual.normal_eq4 _ (C.identity_member G P torsion q core literal)
      z a b c d hq separated)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHResolved
end
