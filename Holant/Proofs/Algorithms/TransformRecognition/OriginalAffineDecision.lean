import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineSystem
import Holant.Proofs.Algorithms.TransformRecognition.StructuredDovetail
import Holant.Proofs.Algorithms.TransformRecognition.FiniteBranchEnumeration


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineDecision
open Holant Holant.Tractable Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)

def InputValid (input : Input arity) : Prop :=
  ∃ w : Fin (Entries arity) → AlgebraicComplex, ∀ i, (input i).Represents (w i : ℂ)

def oneSlot (B : AffineBranch.Branch arity) :
    Fin ((Entries arity+2)+RationalInputSystem.count (body arity B)) :=
  Fin.natAdd (Entries arity+2) (SparseCoefficientInput.oneIndex RationalCompiler.data (body arity B))
def negSlot (B : AffineBranch.Branch arity) :
    Fin ((Entries arity+2)+RationalInputSystem.count (body arity B)) :=
  Fin.natAdd (Entries arity+2) (RationalInputSystem.negativeIndex (body arity B))

noncomputable def originalValues (w : Fin (Entries arity) → AlgebraicComplex) :
    Fin (Entries arity+2) → AlgebraicComplex := Fin.addCases w ![imaginaryUnit,sqrtTwo]
noncomputable def allValues (w : Fin (Entries arity) → AlgebraicComplex) (B : AffineBranch.Branch arity) :
    Fin ((Entries arity+2)+RationalInputSystem.count (body arity B)) → AlgebraicComplex :=
  OriginalCoefficientBindings.values (originalValues arity w) (RationalInputSystem.rationals (body arity B))

theorem originalValues_coe (w : Fin (Entries arity) → AlgebraicComplex) :
    (fun i => (originalValues arity w i : ℂ)) =
      OriginalVariableLayout.boundValues (fun i => (w i : ℂ)) := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [originalValues,OriginalVariableLayout.boundValues]
  | right i => fin_cases i <;> simp [originalValues,OriginalVariableLayout.boundValues,StandardRootCodes.values]

theorem allValues_coe (w : Fin (Entries arity) → AlgebraicComplex) (B : AffineBranch.Branch arity) :
    (fun i => (allValues arity w B i : ℂ)) =
      RationalInputSystem.values (OriginalVariableLayout.boundValues (fun i => (w i : ℂ))) (body arity B) := by
  funext i
  induction i using Fin.addCases with
  | left i => simpa [allValues,RationalInputSystem.values,OriginalCoefficientBindings.values] using congrFun (originalValues_coe arity w) i
  | right i => simp [allValues,RationalInputSystem.values,OriginalCoefficientBindings.values]

theorem allValues_one (w : Fin (Entries arity) → AlgebraicComplex) (B : AffineBranch.Branch arity) :
    allValues arity w B (oneSlot arity B)=1 := by
  unfold allValues oneSlot OriginalCoefficientBindings.values
  rw [Fin.addCases_right]
  change ((1 : ℚ) : AlgebraicComplex)=1
  exact Rat.cast_one
theorem allValues_neg (w : Fin (Entries arity) → AlgebraicComplex) (B : AffineBranch.Branch arity) :
    allValues arity w B (negSlot arity B) = -1 := by
  simp [allValues,negSlot,OriginalCoefficientBindings.values,RationalInputSystem.rational_negative]

theorem target_represents (input : Input arity) (w : Fin (Entries arity) → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ)) (B : AffineBranch.Branch arity) :
    ∀ i, (target arity input B i).Represents (allValues arity w B i : ℂ) := by
  have h := RationalInputSystem.target_represents (OriginalVariableLayout.descriptors input)
    (OriginalVariableLayout.boundValues (fun i => (w i : ℂ)))
    (OriginalVariableLayout.descriptors_represents input _ hw) (body arity B)
  intro i
  have he := congrFun (allValues_coe arity w B) i
  rw [he]
  exact h i

theorem target_valid (input : Input arity) (hv : InputValid arity input) (B : AffineBranch.Branch arity) :
    CertificateDovetail.Valid (target arity input B) (oneSlot arity B) (negSlot arity B) := by
  obtain ⟨w,hw⟩ := hv
  exact ⟨allValues arity w B,target_represents arity input w hw B,
    allValues_one arity w B,allValues_neg arity w B⟩

def branchAnswer (input : Input arity) (hv : InputValid arity input) (B : AffineBranch.Branch arity) : Bool :=
  StructuredDovetail.answer (target arity input B) (oneSlot arity B) (negSlot arity B)
    (system arity B) (target_valid arity input hv B)

def answer (input : Input arity) (hv : InputValid arity input) : Bool :=
  (FiniteBranchEnumeration.commonAffineCodes arity).any (branchAnswer arity input hv)

theorem guard_redundant (w : Fin (Entries arity) → AlgebraicComplex)
    (B : AffineBranch.Branch arity) (z : Fin (Width arity) → ℂ) :
    (∀ e ∈ EncodedGuard.augment (oneSlot arity B) (negSlot arity B) (system arity B),
      aeval z (EncodedSystem.polynomial (fun i => (allValues arity w B i : ℂ)) e)=0) ↔
    (∀ e ∈ system arity B,
      aeval z (EncodedSystem.polynomial (fun i => (allValues arity w B i : ℂ)) e)=0) := by
  constructor
  · intro h e he
    exact h e (List.mem_cons_of_mem _ he)
  · intro h
    have hb := h
    rw [allValues_coe] at hb
    have hg := ((RationalInputSystem.system_zero_iff _ _ _ z).mp hb).2
      (SparseTransform.guard RationalCompiler.data (Extra arity)) (List.mem_cons_self ..)
    have h1 : (allValues arity w B (oneSlot arity B) : ℂ)=1 := by rw [allValues_one]; rfl
    have hn : (allValues arity w B (negSlot arity B) : ℂ) = -1 := by rw [allValues_neg]; rfl
    intro e he
    rcases List.mem_cons.mp he with rfl | he
    · rw [←NullstellensatzSearch.equation_complex]
      change eval₂ (RingHom.id ℂ) z
        (NullstellensatzSearch.equation (fun i => (allValues arity w B i : ℂ))
          (EncodedGuard.equation (oneSlot arity B) (negSlot arity B)))=0
      rw [EncodedGuard.equation_eval _ _ _ h1 hn]
      change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (SparseTransform.guard RationalCompiler.field.toArithmeticData (Extra arity))=0 at hg
      rw [SparseEvaluation.guard_eval] at hg
      simp only [SymbolicTransform.determinant,SymbolicTransform.matrix,
        SparseTransform.point,SymbolicTransform.index,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl] at hg
      exact hg
    · exact h e he

theorem branchAnswer_correct (input : Input arity) (hv : InputValid arity input)
    (w : Fin (Entries arity) → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ)) (B : AffineBranch.Branch arity) :
    branchAnswer arity input hv B=true ↔
      ∃ y : SymbolicTransform.Variables (AffineBranch.Parameters (s:=s)) → ℂ,
        ∀ r, eval₂ (algebraMap AlgebraicComplex ℂ) y
          (AffineBranch.equations (sourceVertex arity w) (sourceEdge arity w) B r)=0 := by
  rw [branchAnswer,StructuredDovetail.answer_correct _ _ (target_represents arity input w hw B)]
  simp_rw [guard_redundant,allValues_coe]
  exact source_solution_iff arity w B

theorem answer_correct (input : Input arity) (hv : InputValid arity input)
    (w : Fin (Entries arity) → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ)) :
    answer arity input hv=true ↔
      AffineBranch.Shared (sourceVertex arity w) (sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) := by
  rw [answer,List.any_eq_true,AffineBranch.shared_iff_solution]
  constructor
  · rintro ⟨B,_,hB⟩
    exact ⟨B,(branchAnswer_correct arity input hv w hw B).mp hB⟩
  · rintro ⟨B,hy⟩
    exact ⟨B,FiniteBranchEnumeration.mem_commonAffineCodes arity B,
      (branchAnswer_correct arity input hv w hw B).mpr hy⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineDecision
