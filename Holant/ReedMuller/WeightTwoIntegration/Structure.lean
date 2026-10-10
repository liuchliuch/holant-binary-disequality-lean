import Holant.ReedMuller.WeightTwoIntegration.CanonicalSix
import Holant.ReedMuller.WeightTwoIntegration.ThreeProduct

/-! The complete algebraic alternative of7.9, independent of resource
membership. The exceptional normal form has literal original-port reindexing. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false

 def ExceptionalForm {n : ℕ} (q : Signature ℂ n) : Prop :=
  ∃d : ExceptionalData,∃p : Fin n ≃ Fin 6,∃c : ℂ,c≠0 ∧
    Tensor.reindex p q=fun x=>c*Signature.coordinateAction (fun _=>walshKernel)
      (ExceptionalTopology.paired d.h) x

 theorem ExceptionalForm.arity {n : ℕ} {q : Signature ℂ n} (h : ExceptionalForm q) : n=6 := by
  obtain ⟨d,p,c,hc,he⟩ := h
  simpa using Fintype.card_congr p

 theorem source_weight_two_structure {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (q : Signature ℂ (n+2)) (hq : q≠0)
    (hn : 6≤n+2) (hdeck : CanonicalMatchingDeck G R q)
    (hW : ∃u v,(weightGraph (walsh q)).Adj u v) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor q ∨ ExceptionalForm q := by
  have ha := actualMatchingDeck_of_canonical R q hdeck
  have H := source_matching_consistency hG hspan R q hq hn hdeck
  have hd := actual_equality_deck hG hspan R q ha
  have hw := actual_weighted_deck hG hspan R q ha
  obtain ⟨u,v,huv⟩ := hW
  let C := originalPairing (by norm_num : (2:ℂ)≠0) (walsh q) H hd hn u v huv
  have hc3 := C.count_ge_three hn
  by_cases hfour : 4≤C.count
  · obtain ⟨rho,hrho⟩ := (C.logical_integration (by norm_num) H hd hw hn).1 hfour
    exact Or.inl (C.physical_factor q hq (by norm_num) H hd hn rho hrho)
  · have hc : C.count=3 := by omega
    have hn4 : n=4 := by have he:=C.arity; omega
    subst n
    obtain ⟨rho,kap,he⟩ := C.three_parameters H hd hw hn hc
    by_cases hk : (kap:ℂ)=1
    · exact Or.inl (C.three_factor q hq hc H hd hn rho kap hk he)
    · let d : ExceptionalData := ⟨(fun i=>(rho i:ℂ)),kap,(fun i=>(rho i).ne_zero),kap.ne_zero,hk,
        C.three_square_relations H hd hw hn hc rho kap hk he⟩
      exact Or.inr ⟨d,(C.canonicalOrder hc).symm,C.logical (fun _=>false),
        C.logical_nonzero (by norm_num) H hd hn _,
        C.canonical_physical q hc H (fun i=>(rho i:ℂ)) kap he⟩

end Holant.ReedMuller.WeightTwoIntegration
