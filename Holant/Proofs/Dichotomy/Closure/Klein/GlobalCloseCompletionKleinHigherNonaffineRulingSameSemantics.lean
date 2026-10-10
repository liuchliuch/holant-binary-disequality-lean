import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRulingCrossSemantics

/-! The complementary same-edge case. Its residual matching and all remaining
factors are independent of the closing kernel; only the exact cycle trace
changes the global scalar, and that trace is allowed to vanish. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
namespace MatchingSurgery
open Holant.Certificates.MatchingContractionClosure
variable {K P J : Type*} [Field K] [DecidableEq P] [Fintype J] [DecidableEq J]

 def castDeletePorts (ports : (J × Bool) ≃ P) (e : J) (u v : P)
     (hu : ports (e,false) = u) (hv : ports (e,true) = v) :
     (OtherEdges e × Bool) ≃ Remaining u v :=
   (deletePorts ports e).trans (Equiv.subtypeEquivRight (fun x => by rw [hu,hv]))

 theorem contract_matched_cast (ports : (J × Bool) ≃ P) (A : J → Binary (K := K)) (weight : K)
     (e : J) (C : Binary (K := K)) (u v : P)
     (hu : ports (e,false) = u) (hv : ports (e,true) = v) :
     contractPair u v C (productValue ports A weight) =
       productValue (castDeletePorts ports e u v hu hv) (fun d => A d.val) (trace (A e) C*weight) := by
   subst u
   subst v
   exact contract_matched ports A weight e C

 variable {r : ℕ}

 theorem edgeIndex_mate (M : Matching P r) (u : P) : edgeIndex M (M.mate u) = edgeIndex M u := by
   obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective u
   rw [M.mate_port]
   simp only [edgeIndex,Equiv.symm_apply_apply]

 def sameOrientedPorts (M : Matching P r) (u : P) : (Fin r × Bool) ≃ P :=
   (flipSlots (sameMask M.ports u)).trans M.ports

 theorem sameOriented_selected (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v) :
     sameOrientedPorts M u (edgeIndex M u,false) = u ∧
       sameOrientedPorts M u (edgeIndex M u,true) = v := by
   apply same_selected_ports M.ports u v huv
   change edgeIndex M u = edgeIndex M v
   rw [←hc,edgeIndex_mate]

 def sameResidualPorts (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v) :
     (OtherEdges (edgeIndex M u) × Bool) ≃ Remaining u v :=
   castDeletePorts (sameOrientedPorts M u) (edgeIndex M u) u v
     (sameOriented_selected M u v huv hc).1 (sameOriented_selected M u v huv hc).2

 def sameMatching (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v) :
     Matching (Remaining u v) (Fintype.card (OtherEdges (edgeIndex M u))) :=
   matching (sameResidualPorts M u v huv hc)

 def sameFactors (M : Matching P r) (u : P) (A : Fin r → Binary (K := K)) :
     OtherEdges (edgeIndex M u) → Binary (K := K) :=
   fun d => orientedFactors A (sameMask M.ports u) d.val

 def sameScalar (M : Matching P r) (u : P) (A : Fin r → Binary (K := K))
     (weight : K) (C : Binary (K := K)) : K :=
   trace (orientedFactors A (sameMask M.ports u) (edgeIndex M u)) C*weight

 def samePresentation (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) : Presentation K (Remaining u v) :=
   Presentation.ofFinite (sameResidualPorts M u v huv hc) (sameFactors M u A) (sameScalar M u A weight C)

 theorem same_presentation_ports (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) :
     (samePresentation M u v huv hc A weight C).ports = (sameMatching M u v huv hc).ports := rfl

 theorem same_card_exact (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) :
     contractPair u v C (productValue M.ports A weight) =
       (samePresentation M u v huv hc A weight C).tensor := by
   rw [samePresentation,Presentation.ofFinite_tensor]
   have ho := reorient_product M.ports A weight (sameMask M.ports u)
   rw [←ho]
   exact contract_matched_cast (sameOrientedPorts M u) _ weight (edgeIndex M u) C u v
     (sameOriented_selected M u v huv hc).1 (sameOriented_selected M u v huv hc).2

 theorem same_presentation_valid {G : Set (Binary (K := K))} (hrev : ReversalStable G)
     (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u = v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K))
     (hA : ∀ e, SafeBinary G (A e)) :
     (samePresentation M u v huv hc A weight C).Valid G := by
   apply Presentation.ofFinite_valid
   intro d
   exact orientedFactors_safe hrev A _ hA d.val

 theorem presentation_zero_of_scalar_zero {Q : Type*} (M : Presentation K Q) (hM : M.scalar = 0) :
     M.tensor = 0 := by
   funext x
   simp only [Presentation.tensor,productValue,hM,zero_mul,Pi.zero_apply]

end MatchingSurgery
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
