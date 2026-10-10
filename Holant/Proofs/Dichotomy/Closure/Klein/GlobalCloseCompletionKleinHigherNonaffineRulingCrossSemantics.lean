import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRulingCrossPorts
import Holant.Certificates.MatchingContractionClosure.NonzeroProducts

/-! Generic-field tensor semantics for the shared disagreement-preserving
crossMatching. The exact residual ports are fixed independently of matrices,
labels and kernel choices; cross contractions retain their nonzero scalar. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
namespace MatchingSurgery
open Holant.Certificates.MatchingContractionClosure
variable {K P J : Type*} [Field K] [DecidableEq P] [Fintype J] [DecidableEq J]

 theorem contract_cross_cast (ports : (J × Bool) ≃ P) (A : J → Binary (K := K)) (weight : K)
     (e f : J) (hef : e ≠ f) (C : Binary (K := K)) (u v : P)
     (hu : ports (e,true) = u) (hv : ports (f,false) = v) :
     contractPair u v C (productValue ports A weight) =
       productValue (castSplicePorts ports e f u v hu hv) (spliceFactors C A e f) weight := by
   subst u
   subst v
   exact contract_cross ports A weight e f hef C

 theorem orientedFactors_nonsingular (A : J → Binary (K := K)) (mask : J → Bool)
     (hA : ∀ e, Matrix.det (A e) ≠ 0) : ∀ e, Matrix.det (orientedFactors A mask e) ≠ 0 := by
   intro e
   unfold orientedFactors
   split
   · rw [Matrix.det_transpose]
     exact hA e
   · exact hA e

 variable {r : ℕ}

 def crossFactors (M : Matching P r) (u v : P) (A : Fin r → Binary (K := K)) (C : Binary (K := K)) :
     OtherEdges (edgeIndex M v) → Binary (K := K) :=
   spliceFactors C (orientedFactors A (crossMask M.ports u v)) (edgeIndex M u) (edgeIndex M v)

 def crossPresentation (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) : Presentation K (Remaining u v) :=
   Presentation.ofFinite (crossResidualPorts M u v huv hc) (crossFactors M u v A C) weight

 theorem cross_presentation_ports (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) :
     (crossPresentation M u v huv hc A weight C).ports = (crossMatching M u v huv hc).ports := rfl

 theorem cross_presentation_scalar (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) :
     (crossPresentation M u v huv hc A weight C).scalar = weight := rfl

/-- Exact physical tensor equality for ANY chosen matrix kernel. -/
 theorem cross_card_exact (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K)) :
     contractPair u v C (productValue M.ports A weight) =
       (crossPresentation M u v huv hc A weight C).tensor := by
   rw [crossPresentation,Presentation.ofFinite_tensor]
   have ho := reorient_product M.ports A weight (crossMask M.ports u v)
   rw [←ho]
   exact contract_cross_cast (crossOrientedPorts M u v) _ weight
     (edgeIndex M u) (edgeIndex M v) (edgeIndex_ne M u v huv hc) C u v
       (crossOriented_selected M u v huv hc).1 (crossOriented_selected M u v huv hc).2

 theorem cross_factors_nonsingular (M : Matching P r) (u v : P)
     (A : Fin r → Binary (K := K)) (C : Binary (K := K))
     (hA : ∀ e, Matrix.det (A e) ≠ 0) (hC : Matrix.det C ≠ 0) :
     ∀ e, Matrix.det (crossFactors M u v A C e) ≠ 0 :=
   spliceFactors_nonsingular C _ _ _ hC (orientedFactors_nonsingular A _ hA)

 theorem cross_card_nonzero (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K))
     (hA : ∀ e, Matrix.det (A e) ≠ 0) (hweight : weight ≠ 0) (hC : Matrix.det C ≠ 0) :
     contractPair u v C (productValue M.ports A weight) ≠ 0 := by
   rw [cross_card_exact M u v huv hc A weight C,crossPresentation,Presentation.ofFinite_tensor]
   exact productValue_nonzero _ _ _ (cross_factors_nonsingular M u v A C hA hC) hweight

 theorem cross_presentation_valid {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
     (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
     (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (A : Fin r → Binary (K := K)) (weight : K) (C : Binary (K := K))
     (hA : ∀ e, SafeBinary G (A e)) (hC : SafeBinary G C) :
     (crossPresentation M u v huv hc A weight C).Valid G := by
   apply Presentation.ofFinite_valid
   exact spliceFactors_safe hG hX C _ _ _ hC (orientedFactors_safe hrev A _ hA)

 theorem cross_edges (M : Matching P r) (v : P) :
     Fintype.card (OtherEdges (edgeIndex M v)) = r-1 := by
   simpa only [OtherEdges,Fintype.card_fin,Fintype.card_unique] using
     Fintype.card_subtype_compl (fun e : Fin r => e = edgeIndex M v)

end MatchingSurgery
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
