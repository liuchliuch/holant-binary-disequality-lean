import Holant.Proofs.Algorithms.TransformRecognition.FiniteSystemDisjunction
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineBranchMachine


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineDisjunction
set_option backward.isDefEq.respectTransparency false
open Holant Holant.Tractable Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open OriginalAffineSystem
variable {s : ℕ} (arity : Fin s → ℕ)

def branches : List (List (Sparse.Poly (Width arity) 1)) :=
  (FiniteBranchEnumeration.commonAffineCodes arity).map (body arity)
def combined : List (Sparse.Poly (Width arity) 1) :=
  SparseTransform.guard RationalCompiler.data (Extra arity) ::
    FiniteSystemDisjunction.combine (branches arity)

theorem combined_zero_iff (z : Fin (Width arity) → ℂ) :
    (∀ p ∈ combined arity, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
    ∃ B : AffineBranch.Branch arity,
      ∀ p ∈ body arity B, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  rw [combined,List.forall_mem_cons,FiniteSystemDisjunction.combine_zero_iff]
  constructor
  · rintro ⟨_,S,hS,hz⟩
    obtain ⟨B,_,rfl⟩ := List.mem_map.mp hS
    exact ⟨B,hz⟩
  · rintro ⟨B,hB⟩
    exact ⟨hB _ (List.mem_cons_self ..),body arity B,
      List.mem_map.mpr ⟨B,FiniteBranchEnumeration.mem_commonAffineCodes arity B,rfl⟩,hB⟩

theorem bound_solution_iff (w : Fin (Entries arity) → AlgebraicComplex) :
    (∃ z : Fin (Width arity) → ℂ, Bound arity w z ∧
      ∀ p ∈ combined arity, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) ↔
    AffineBranch.Shared (sourceVertex arity w) (sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) := by
  rw [AffineBranch.shared_iff_solution]
  constructor
  · rintro ⟨z,hb,hz⟩
    obtain ⟨B,hB⟩ := (combined_zero_iff arity z).mp hz
    refine ⟨B,?_⟩
    apply (source_solution_iff arity w B).mp
    exact ⟨z,(RationalInputSystem.system_zero_iff _ _ _ z).mpr ⟨hb,hB⟩⟩
  · rintro ⟨B,hB⟩
    obtain ⟨z,hz⟩ := (source_solution_iff arity w B).mpr hB
    obtain ⟨hb,hr⟩ := (RationalInputSystem.system_zero_iff _ _ _ z).mp hz
    exact ⟨z,hb,(combined_zero_iff arity z).mpr ⟨B,hr⟩⟩

def answer (input : Input arity) (hv : OriginalAffineDecision.InputValid arity input) : Bool :=
  OriginalSystemDecision.answer (OriginalVariableLayout.descriptors input)
    (OriginalAffineBranchMachine.descriptors_valid arity input hv)
    (combined arity) (OriginalVariableLayout.binding (Entries arity) (s+1))

theorem answer_correct (input : Input arity) (hv : OriginalAffineDecision.InputValid arity input)
    (w : Fin (Entries arity) → AlgebraicComplex)
    (hw : ∀ i, (input i).Represents (w i : ℂ)) :
    answer arity input hv=true ↔
      AffineBranch.Shared (sourceVertex arity w) (sourceEdge arity w) (algebraMap AlgebraicComplex ℂ) := by
  have hd : ∀ i, (OriginalVariableLayout.descriptors input i).Represents
      (OriginalAffineDecision.originalValues arity w i : ℂ) := by
    intro i
    rw [congrFun (OriginalAffineDecision.originalValues_coe arity w) i]
    exact OriginalVariableLayout.descriptors_represents input (fun i => (w i : ℂ)) hw i
  rw [answer,OriginalSystemDecision.answer_correct _ _ _ hd (combined arity) _ (by exact List.mem_cons_self ..)]
  simp only [OriginalAffineDecision.originalValues_coe]
  simp_rw [RationalInputSystem.system_zero_iff]
  exact bound_solution_iff arity w

theorem answer_eq_finite_search (input : Input arity) (hv : OriginalAffineDecision.InputValid arity input) :
    answer arity input hv=OriginalAffineDecision.answer arity input hv := by
  obtain ⟨w,hw⟩ := hv
  apply Bool.eq_iff_iff.mpr
  exact (answer_correct arity input ⟨w,hw⟩ w hw).trans
    (OriginalAffineDecision.answer_correct arity input ⟨w,hw⟩ w hw).symm

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineDisjunction
