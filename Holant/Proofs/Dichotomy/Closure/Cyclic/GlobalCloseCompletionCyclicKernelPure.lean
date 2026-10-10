import Holant.Proofs.Dichotomy.Closure.Cyclic.GlobalCloseCompletionCyclicKernelPencil
import Holant.ReedMuller.FixedCoreDeck.WalshMatching

/-! For an RM-supported Walsh row, two actual safe matching cards force
any invertible I/X-pencil kernel to be pure I or pure X. No finite group
cardinality or literal C2 matching premise is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelPure
open Holant Holant.ReedMuller.CoefficientAtlas
open Holant.Certificates.MatchingContractionClosure
namespace P
export GlobalCloseCompletionCyclicKernelPencil (pencil weightedCard walsh_physical_pencil weighted_repeated)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false

def toAtlas (M : Holant.ReedMuller.FixedCoreDeck.WeightedMatching 6 3) : WeightedMatching where
  ports := (Equiv.prodCongr (Equiv.refl (Fin 3)) finTwoEquiv).trans M.ports
  scalar := Units.mk0 M.constant M.constant_ne_zero
  ratio i := Units.mk0 (M.ratio i) (M.ratio_ne_zero i)

theorem toAtlas_value (M : Holant.ReedMuller.FixedCoreDeck.WeightedMatching 6 3) :
    (toAtlas M).value=M.value := by
  funext w
  rw [M.value_eq_ratioProduct]
  rfl

theorem pencil_eigenvalues (a b : ℂ) (nonsingular : Matrix.det (P.pencil a b)≠0) :
    a+b≠0 ∧ a-b≠0 := by
  have he : Kernel.mul (P.pencil a b) Signature.disequality=
      (fun u v=>b*Signature.equality u v+a*Signature.disequality u v) := by
    funext u v
    cases u <;> cases v <;> simp [P.pencil,Kernel.mul,Signature.equality,Signature.disequality]
  have plus:=Holant.ReedMuller.FixedCoreDeck.transferDiagonal_ne_zero (P.pencil a b) b a he nonsingular false
  have minus:=Holant.ReedMuller.FixedCoreDeck.transferDiagonal_ne_zero (P.pencil a b) b a he nonsingular true
  change (a+b)/2≠0 at plus
  change (a-b)/2≠0 at minus
  exact ⟨fun h=>plus (by rw [h,zero_div]),fun h=>minus (by rw [h,zero_div])⟩

variable (G : Set (Binary (K:=ℂ))) (group : ProjectiveMatrixGroup G)
variable (span : ∀T∈G,∃a b : ℂ,T=P.pencil a b)
include group span in
theorem matching_walsh (h : Signature ℂ 6) (matching : MatchingOrZero G h) :
    walsh h=0 ∨ ∃M : WeightedMatching,M.value=walsh h := by
  rcases Holant.ReedMuller.FixedCoreDeck.walsh_matchingOrZero group span matching with
    zero|⟨r,M,equation⟩
  · exact Or.inl zero
  · have size:=Fintype.card_congr M.ports
    simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at size
    have hr : r=3 := by omega
    subst r
    exact Or.inr ⟨toAtlas M,(toAtlas_value M).trans equation⟩

include group span in
theorem kernel_pure (f : Signature ℂ 8) (support : SupportRM (walsh f))
    (a b : ℂ) (nonsingular : Matrix.det (P.pencil a b)≠0)
    (identity : MatchingOrZero G (physicalCard f 0 false))
    (weighted : MatchingOrZero G (Signature.contract (P.pencil a b) (Tensor.reindex (ports 0).symm f))) :
    a*b=0 := by
  obtain ⟨plus,minus⟩ := pencil_eigenvalues a b nonsingular
  have hI (t : Fin 3→Bool) : walsh (physicalCard f 0 false) (repeatedWord t)≠0 := by
    rw [walsh_physical_plus]
    exact plusCard_repeated_nonzero support _ _
  have hT (t : Fin 3→Bool) :
      walsh (Signature.contract (P.pencil a b) (Tensor.reindex (ports 0).symm f)) (repeatedWord t)≠0 := by
    rw [P.walsh_physical_pencil,P.weighted_repeated support]
    apply mul_ne_zero _ (plusCard_repeated_nonzero support _ _)
    cases GlobalCloseCompletionCyclicKernelCross.parity t <;> assumption
  obtain ⟨M,hM⟩ : ∃M : WeightedMatching,M.value=walsh (physicalCard f 0 false) := by
    rcases matching_walsh G group span _ identity with zero|matching
    · exact False.elim ((hI (fun _=>false)) (congrFun zero _))
    · exact matching
  obtain ⟨N,hN⟩ : ∃N : WeightedMatching,N.value=
      walsh (Signature.contract (P.pencil a b) (Tensor.reindex (ports 0).symm f)) := by
    rcases matching_walsh G group span _ weighted with zero|matching
    · exact False.elim ((hT (fun _=>false)) (congrFun zero _))
    · exact matching
  apply GlobalCloseCompletionCyclicKernelCross.pencil_separated M N
    (fun t=>by rw [hM];exact hI t) a b plus minus
  intro t
  rw [hN,P.walsh_physical_pencil,P.weighted_repeated support,hM,walsh_physical_plus]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionCyclicKernelPure
end
