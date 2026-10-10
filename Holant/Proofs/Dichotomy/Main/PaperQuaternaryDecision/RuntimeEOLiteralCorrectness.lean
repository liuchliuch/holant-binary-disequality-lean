import Holant.Proofs.Recognition.RuntimeEOLiteralCorrectness
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeEOLiteralRequestSource
import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeTensorRequestSource
import Holant.Proofs.Tractability.EOEvaluation.EOConditionCertificate.LiteralProduct

/-! Exact literal A/P meaning of the runtime pair-view root search. Existential
complex parameter values descend to algebraic class witnesses only in the
semantic theorem. The returned bytes are the unchanged actual combined-system
root candidate, not these proof-side factors or a successful template index. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralCorrectness
open Holant.LocalDrafts.RemoteWork.TractChainV1
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.Tractability.EOEvaluation.EOConditionCertificate
open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm (Parameter)
open _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralRequestSource
open UniformTensorWitnessBranch (Metadata)
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {s : ℕ} (arity : Fin s → ℕ) (G : (j : Fin s) → Signature AlgebraicComplex (arity j))

def Bound (product : Bool) (count : ℕ) (z : Fin (Width arity product count) → ℂ) : Prop :=
  ∀j,z (bindings arity product count j)=(UniformKPolynomial.values arity G j : ℂ)

theorem bound_old (product : Bool) (count : ℕ) (z : Fin (Width arity product count) → ℂ)
    (hb : Bound arity G product count z) :
    OriginalTensorRows.Bound arity (parameters product count) (OriginalFamilyInput.values arity G false) z :=
  fun j => (hb j).trans (congrFun (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.values_coe arity G) j)

theorem bound_imaginary (product : Bool) (count : ℕ) (z : Fin (Width arity product count) → ℂ)
    (hb : Bound arity G product count z) : z (imaginary arity product count)=(imaginaryUnit : ℂ) :=
  OriginalVariableLayout.binding_imaginary z _ (bound_old arity G product count z hb)

theorem bound_sqrt (product : Bool) (count : ℕ) (z : Fin (Width arity product count) → ℂ)
    (hb : Bound arity G product count z) : z (sqrt arity product count)=(sqrtTwo : ℂ) :=
  OriginalVariableLayout.binding_sqrt z _ (bound_old arity G product count z hb)

theorem bound_entry (product : Bool) (count : ℕ) (z : Fin (Width arity product count) → ℂ)
    (hb : Bound arity G product count z) (i : Fin s) (x : Fin (arity i) → Bool) :
    z (address arity product count i x)=(G i x : ℂ) := by
  have h := OriginalTensorRows.bound_entry arity (parameters product count) (OriginalFamilyInput.values arity G false) z
    (bound_old arity G product count z hb) (.inl i) x
  change z (address arity product count i x)=(OriginalAffineSystem.sourceVertex arity (OriginalFamilyInput.values arity G false) i x : ℂ) at h
  rw [OriginalFamilyInput.sourceVertex_values] at h
  exact h

def fill (product : Bool) (count : ℕ) (u : Fin (parameters product count) → ℂ) :
    Fin (Width arity product count) → ℂ :=
  OriginalVariableLayout.fill ![1,0,0,1,1] u
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) OriginalVariableLayout.constants

theorem fill_bound (product : Bool) (count : ℕ) (u : Fin (parameters product count) → ℂ) :
    Bound arity G product count (fill arity G product count u) := by
  intro j
  exact (OriginalVariableLayout.fill_binding _ u _ j).trans
    (congrFun (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorRequestSource.values_coe arity G) j).symm

theorem fill_guard (product : Bool) (count : ℕ) (u : Fin (parameters product count) → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) (fill arity G product count u)
      (SparseTransform.guard RationalCompiler.data (Extra arity product count))=0 := by
  rw [_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeTensorBasisSemantics.compilerData,SparseEvaluation.guard_eval]
  simp [fill,SymbolicTransform.determinant,SymbolicTransform.matrix,SparseTransform.point,
    SymbolicTransform.index,OriginalVariableLayout.fill]

theorem fill_scale (count : ℕ) (c : ℂ) : fill arity G false count (fun _ => c) (scale arity count)=c := by
  exact OriginalVariableLayout.fill_parameter ![1,0,0,1,1] (fun _ : Fin 1 => c)
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) OriginalVariableLayout.constants 0

def productValues {count : ℕ} (theta : Parameter count → ℂ) : Fin (1+2*count) → ℂ :=
  Function.extend parameterIndex theta (fun _ => 0)

theorem fill_parameter {count : ℕ} (theta : Parameter count → ℂ) (t : Parameter count) :
    fill arity G true count (productValues theta) (parameter arity t)=theta t := by
  exact (OriginalVariableLayout.fill_parameter ![1,0,0,1,1] (productValues theta)
    (fun j => (OriginalFamilyInput.values arity G false j : ℂ)) OriginalVariableLayout.constants
    (parameterIndex t)).trans (parameterIndex_injective.extend_apply theta (fun _ => 0) t)

variable (i : Fin s) (complete : Bool) (k : ℕ) (m : Metadata)
    (hg : m∈RuntimeTensorCatalogue.catalogue (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (arity i,complete,k)))
    (hv : RuntimeEOPairings.valid (_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOView.arity (arity i,complete,k)) m=true)
local notation "p" => RuntimeEOPairings.pairing m hg hv

def restricted : Signature AlgebraicComplex (p).count :=
  fun x => _root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralTable.viewSignature (G i) complete k ((p).word x)

theorem affine_body_iff (z : Fin (Width arity false m.1.length) → ℂ) (hb : Bound arity G false m.1.length z) :
    (∀e∈typedBody arity i complete k m hg hv false,SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (SparseTransform.guard RationalCompiler.data (Extra arity false m.1.length))=0 ∧
    ∃C : AffineNormalForm.Code (p).count,∀x,
      (restricted arity G i complete k m hg hv x : ℂ)=z (scale arity m.1.length)*(AffineNormalForm.formula C 1 x : ℂ) := by
  change (∀e∈_::_,_) ↔ _
  rw [List.forall_mem_cons,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralSystems.affine_equations_iff _ _ _ complete k m hg hv (G i) z
    (bound_imaginary arity G false m.1.length z hb) (bound_sqrt arity G false m.1.length z hb)
    (bound_entry arity G false m.1.length z hb i)]
  rfl

theorem product_body_iff (z : Fin (Width arity true m.1.length) → ℂ) (hb : Bound arity G true m.1.length z) :
    (∀e∈typedBody arity i complete k m hg hv true,SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (SparseTransform.guard RationalCompiler.data (Extra arity true m.1.length))=0 ∧
    ∃S : Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.Skeleton (p).count,∀x,
      (restricted arity G i complete k m hg hv x : ℂ)=
        Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.evaluate S (fun t => z (parameter arity t)) x := by
  change (∀e∈_::_,_) ↔ _
  rw [List.forall_mem_cons,_root_.Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralSystems.product_equations_iff _ _ _ complete k m hg hv (G i) z
    (bound_imaginary arity G true m.1.length z hb) (bound_sqrt arity G true m.1.length z hb)
    (bound_entry arity G true m.1.length z hb i)]
  rfl

theorem affine_solutions_iff :
    (∃z : Fin (Width arity false m.1.length) → ℂ,Bound arity G false m.1.length z ∧
      ∀e∈typedBody arity i complete k m hg hv false,SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    Affine (restricted arity G i complete k m hg hv) := by
  rw [AffineNormalForm.affine_iff]
  constructor
  · rintro ⟨z,hb,he⟩
    obtain ⟨_,C,hC⟩ := (affine_body_iff arity G i complete k m hg hv z hb).mp he
    exact ⟨C,(LiteralAffine.scalar_descent C _).mp ⟨_,hC⟩⟩
  · rintro ⟨C,hC⟩
    obtain ⟨c,hc⟩ := (LiteralAffine.scalar_descent C _).mpr hC
    let z := fill arity G false m.1.length (fun _ => c)
    have hb := fill_bound arity G false m.1.length (fun _ => c)
    refine ⟨z,hb,(affine_body_iff arity G i complete k m hg hv z hb).mpr ⟨fill_guard arity G false m.1.length _,C,?_⟩⟩
    intro x
    rw [show z (scale arity m.1.length)=c from fill_scale arity G _ c]
    exact hc x

theorem product_solutions_iff :
    (∃z : Fin (Width arity true m.1.length) → ℂ,Bound arity G true m.1.length z ∧
      ∀e∈typedBody arity i complete k m hg hv true,SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z e=0) ↔
    Product (restricted arity G i complete k m hg hv) := by
  rw [Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm.product_iff]
  constructor
  · rintro ⟨z,hb,he⟩
    obtain ⟨_,S,hS⟩ := (product_body_iff arity G i complete k m hg hv z hb).mp he
    exact ⟨S,(LiteralProduct.parameter_descent S _).mp ⟨_,hS⟩⟩
  · rintro ⟨S,hS⟩
    obtain ⟨theta,ht⟩ := (LiteralProduct.parameter_descent S _).mpr hS
    let z := fill arity G true m.1.length (productValues theta)
    have hb := fill_bound arity G true m.1.length (productValues theta)
    refine ⟨z,hb,(product_body_iff arity G i complete k m hg hv z hb).mpr ⟨fill_guard arity G true m.1.length _,S,?_⟩⟩
    intro x
    have hz : (fun t => z (parameter arity t))=theta := funext (fill_parameter arity G theta)
    erw [hz]
    exact ht x

variable (input : OriginalFamilyInput.Input arity) (represented : ∀j x,(input j x).Represents (G j x : ℂ))

theorem output_correct (product : Bool) :
    (output arity input i complete k m hg hv G represented product).isSome=true ↔
      if product then Product (restricted arity G i complete k m hg hv)
      else Affine (restricted arity G i complete k m hg hv) := by
  rw [output_isSome_iff]
  cases product
  · exact affine_solutions_iff arity G i complete k m hg hv
  · exact product_solutions_iff arity G i complete k m hg hv

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecision.RuntimeEOLiteralCorrectness
