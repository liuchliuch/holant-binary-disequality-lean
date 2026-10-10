import Holant.Proofs.Algorithms.TransformRecognition.RationalInputSystem
import Holant.Proofs.Algorithms.TransformRecognition.StructuredDovetail
import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemDecision
open Holant.Tractable MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Sparse
variable {m q : ℕ}

def Valid (input : Fin m → RootCode) : Prop :=
  ∃ w : Fin m → AlgebraicComplex, ∀ i, (input i).Represents (w i : ℂ)

def oneSlot (S : List (Poly (5+q) 1)) : Fin (m+RationalInputSystem.count S) :=
  Fin.natAdd m (SparseCoefficientInput.oneIndex RationalCompiler.data S)
def negSlot (S : List (Poly (5+q) 1)) : Fin (m+RationalInputSystem.count S) :=
  Fin.natAdd m (RationalInputSystem.negativeIndex S)

noncomputable def values (w : Fin m → AlgebraicComplex) (S : List (Poly (5+q) 1)) :
    Fin (m+RationalInputSystem.count S) → AlgebraicComplex :=
  OriginalCoefficientBindings.values w (RationalInputSystem.rationals S)

theorem values_coe (w : Fin m → AlgebraicComplex) (S : List (Poly (5+q) 1)) :
    (fun i => (values w S i : ℂ)) = RationalInputSystem.values (fun i => (w i : ℂ)) S := by
  funext i
  induction i using Fin.addCases with
  | left i => simp [values,RationalInputSystem.values,OriginalCoefficientBindings.values]
  | right i => simp [values,RationalInputSystem.values,OriginalCoefficientBindings.values]

theorem values_one (w : Fin m → AlgebraicComplex) (S : List (Poly (5+q) 1)) :
    values w S (oneSlot S)=1 := by
  unfold values oneSlot OriginalCoefficientBindings.values
  rw [Fin.addCases_right]
  change ((1 : ℚ) : AlgebraicComplex) = 1
  exact Rat.cast_one
theorem values_neg (w : Fin m → AlgebraicComplex) (S : List (Poly (5+q) 1)) :
    values w S (negSlot S) = -1 := by
  simp [values,negSlot,OriginalCoefficientBindings.values,RationalInputSystem.rational_negative]

theorem target_represents (input : Fin m → RootCode) (w : Fin m → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ)) (S : List (Poly (5+q) 1)) :
    ∀ i, (RationalInputSystem.target input S i).Represents (values w S i : ℂ) := by
  have h := RationalInputSystem.target_represents input (fun i => (w i : ℂ)) hw S
  simpa only [←values_coe] using h

theorem target_valid (input : Fin m → RootCode) (hv : Valid input) (S : List (Poly (5+q) 1)) :
    CertificateDovetail.Valid (RationalInputSystem.target input S) (oneSlot S) (negSlot S) := by
  obtain ⟨w,hw⟩ := hv
  exact ⟨values w S,target_represents input w hw S,values_one w S,values_neg w S⟩

def answer (input : Fin m → RootCode) (hv : Valid input) (S : List (Poly (5+q) 1))
    (address : Fin m → Fin (5+q)) : Bool :=
  StructuredDovetail.answer (RationalInputSystem.target input S) (oneSlot S) (negSlot S)
    (RationalInputSystem.system S address) (target_valid input hv S)

theorem guard_redundant (w : Fin m → AlgebraicComplex) (S : List (Poly (5+q) 1))
    (address : Fin m → Fin (5+q))
    (hg : SparseTransform.guard RationalCompiler.data q ∈ S) (z : Fin (5+q) → ℂ) :
    (∀ e ∈ EncodedGuard.augment (oneSlot S) (negSlot S) (RationalInputSystem.system S address),
      aeval z (EncodedSystem.polynomial (fun i => (values w S i : ℂ)) e)=0) ↔
    (∀ e ∈ RationalInputSystem.system S address,
      aeval z (EncodedSystem.polynomial (fun i => (values w S i : ℂ)) e)=0) := by
  constructor
  · intro h e he
    exact h e (List.mem_cons_of_mem _ he)
  · intro h e he
    rcases List.mem_cons.mp he with rfl | he
    · have hr := h
      rw [values_coe] at hr
      have hguard := ((RationalInputSystem.system_zero_iff _ S address z).mp hr).2 _ hg
      have h1 : (values w S (oneSlot S) : ℂ)=1 := by rw [values_one]; rfl
      have hn : (values w S (negSlot S) : ℂ) = -1 := by rw [values_neg]; rfl
      rw [←NullstellensatzSearch.equation_complex]
      change eval₂ (RingHom.id ℂ) z
        (NullstellensatzSearch.equation (fun i => (values w S i : ℂ))
          (EncodedGuard.equation (oneSlot S) (negSlot S)))=0
      rw [EncodedGuard.equation_eval _ _ _ h1 hn]
      change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
        (SparseTransform.guard RationalCompiler.field.toArithmeticData q)=0 at hguard
      rw [SparseEvaluation.guard_eval] at hguard
      simp only [SymbolicTransform.determinant,SymbolicTransform.matrix,
        SparseTransform.point,SymbolicTransform.index,Bool.false_eq_true,ite_false,ite_true,Sum.elim_inl] at hguard
      exact hguard
    · exact h e he

theorem answer_correct (input : Fin m → RootCode) (hv : Valid input)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (S : List (Poly (5+q) 1)) (address : Fin m → Fin (5+q))
    (hg : SparseTransform.guard RationalCompiler.data q ∈ S) :
    answer input hv S address=true ↔
      ∃ z : Fin (5+q) → ℂ, ∀ e ∈ RationalInputSystem.system S address,
        aeval z (EncodedSystem.polynomial (RationalInputSystem.values (fun i => (w i : ℂ)) S) e)=0 := by
  rw [answer,StructuredDovetail.answer_correct _ _ (target_represents input w hw S)]
  simp_rw [guard_redundant w S address hg,values_coe]

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemDecision
