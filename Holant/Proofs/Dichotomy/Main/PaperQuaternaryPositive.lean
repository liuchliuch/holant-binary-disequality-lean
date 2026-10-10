import Holant.EightVertex.RetainedInterface
import Holant.Proofs.Algorithms.TractCoreSource
import Holant.Proofs.Dichotomy.Main.PaperLiteralEqualityCriterion

/-! Exact positive branch of the independent no-I quaternary theorem.
The endpoint excludes the two EO clauses; every remaining alternative runs
an actual evaluator on the unchanged original family and answer field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryPositive
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines Holant.LocalDrafts.MainChain
open Holant.EightVertex.ProductAnchor
namespace RI
export Holant.EightVertex.RetainedInterface (no_eo_clauses survives)
end RI
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
abbrev family:=PaperLiteralEqualityCriterion.family G
abbrev encoding:=RawClosedNetwork.validatedEncoding s 1 a
abbrev presentation:=PaperLiteralEqualityCriterion.presentation G
abbrev value:=PaperLiteralEqualityCriterion.value G
variable {q : Signature AlgebraicComplex 4}
variable (hq : (⟨4,q⟩ : AnySignature AlgebraicComplex)∈family G) (he : EndpointEven q)

def matchingComputes
    (hm : MatchingAlternative (preprocess (familyAction sourceKBasis (family G)))) :
    Computes (encoding (s:=s) (a:=a)) (presentation G).encoding (value G) := by
  let KG := KSourceTransport.ordinarySignatures G
  have hKG : ∀i : Fin s,(⟨a i.val,KG i⟩ : AnySignature AlgebraicComplex)∈
      familyAction sourceKBasis (family G) := fun i => ⟨_,⟨i,rfl⟩,rfl⟩
  let w := TractCoreSource.matchingComputes KG (familyAction sourceKBasis (family G)) hKG hm
  let convert := FamilyAnswerTransport.computes
    (OriginalFamily.coefficient G KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient KG KSourceTransport.equalityEdges)
    (OriginalFamily.coefficient_algebraic G KSourceTransport.nativeEdges)
    (OriginalFamily.coefficient_algebraic KG KSourceTransport.equalityEdges)
  apply congrComputes (w.andThen convert)
  intro r
  exact FamilyAnswerTransport.recover_exact _ _ _ _ (KSourceTransport.ordinary_value_exact G r).symm

include hq he in
/-- All seven source clauses are consumed. The endpoint internally excludes
the two EO clauses, while the other FIVE branches run existing real machines.
Neither an evaluator nor successful recognition is supplied. -/
theorem positive_machine_exists (h : Tract (familyAction sourceKBasis (family G))) :
    Nonempty (Computes (encoding (s:=s) (a:=a)) (presentation G).encoding (value G)) := by
  have exclude := RI.no_eo_clauses (RI.survives hq he) he
  have reduced (hc : TractXCore (preprocess (familyAction sourceKBasis (family G)))) :
      Nonempty (Computes (encoding (s:=s) (a:=a)) (presentation G).encoding (value G)) :=
    ⟨TractXCoreSource.nativeComputesOfKTractX G (family G) (fun i => ⟨i,rfl⟩)
      (Set.finite_range _) ⟨h.1,hc⟩⟩
  rcases h.2 with ho|hs|ht|hm|ha|hp|hl
  · rw [Conformal.preprocess_familyAction] at ho
    exact (exclude.1 ho).elim
  · rw [Conformal.preprocess_familyAction] at hs
    exact (exclude.2 hs).elim
  · exact reduced (Or.inl ht)
  · exact ⟨matchingComputes G hm⟩
  · exact reduced (Or.inr (Or.inl ha))
  · exact reduced (Or.inr (Or.inr (Or.inl hp)))
  · exact reduced (Or.inr (Or.inr (Or.inr hl)))

def computesOfTract (h : Tract (familyAction sourceKBasis (family G))) :
    Computes (encoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  Classical.choice (positive_machine_exists G hq he h)

include hq he in
theorem inFP_of_tract (h : Tract (familyAction sourceKBasis (family G))) :
    InFP (encoding (s:=s) (a:=a)) (presentation G).encoding (value G) :=
  (computesOfTract G hq he h).inFP

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryPositive
end
