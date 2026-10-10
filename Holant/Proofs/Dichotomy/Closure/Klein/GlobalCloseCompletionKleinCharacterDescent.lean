import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterCards
import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinCharacterLocalization

/-! An actual non-character-flat even row of arity at least ten yields a
smaller actual non-character-flat output. The lower-output alternative is
proved internally; no family classifier or arbitrary-output closure is an
input. This is a universal finite-resource descent, not an assertion that the
small non-character-flat output is nonaffine (H6 is a genuine exception). -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterDescent
open Holant Holant.Tractable Holant.LocalDrafts.MainChain Holant.ReedMuller
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.CharacterRecognition
open Holant.ReedMuller.CharacterRecognition.SignedTransport
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace C
export GlobalCloseCompletionKleinCharacterResources (bell)
end C
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding)
end A
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [CharZero K]
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (bells : ∀d l,Gadget.RealizesUpTo F .disequality (C.bell d l))
variable (c : K) (hc : c≠0) (rmActual : Gadget.Realizes F .disequality (c • R.rm))

include bells hc rmActual in
theorem character_of_lower {n : ℕ} (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)
    (hn : 10≤n+2) (even : _root_.Even (n+2))
    (lower : ∀m : ℕ,m<n+2→∀q : Signature K m,Gadget.Realizes F .disequality q→
      CFlat (RH.mapSignature (A.complexEmbedding phi) q)) :
    CFlat (RH.mapSignature (A.complexEmbedding phi) f) := by
  by_cases zero : f=0
  · left
    funext x
    simp [RH.mapSignature,zero]
  let g := RH.mapSignature phi f
  have nonzero : g≠0 := by
    intro hz
    apply zero
    funext x
    apply phi.injective
    have h := congrFun hz x
    simpa only [g,RH.mapSignature,Pi.zero_apply,map_zero] using h
  have cards : CFlatSignedRadonCards (fun y=>(g (wordVector y):ℂ)) := by
    intro v hv
    obtain ⟨frame,direction,outputs⟩ := GlobalCloseCompletionKleinCharacterCards.actual_cards
      phi F bells c hc rmActual f actual v hv
    refine ⟨frame,direction,?_⟩
    intro d l
    obtain ⟨q,actualQ,flatQ⟩ := outputs d l
    exact flatQ (lower n (by omega) q actualQ)
  have affine : Affine g := by
    by_contra bad
    obtain ⟨m,q,bound,_positive,_nonzero,actualQ,badQ⟩ :=
      GlobalCloseCompletionKleinCharacterLocalization.from_signed_cards
        phi F bells c hc rmActual f actual hn even cards bad
    exact badQ (affine_of_CFlat _ (lower m (by omega) q actualQ))
  exact source_affine_to_character_radon_even hn even g affine nonzero cards

include bells hc rmActual in
theorem smaller_noncharacter {n : ℕ} (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)
    (hn : 10≤n+2) (even : _root_.Even (n+2))
    (bad : ¬CFlat (RH.mapSignature (A.complexEmbedding phi) f)) :
    ∃m : ℕ,∃q : Signature K m,m<n+2 ∧ Gadget.Realizes F .disequality q ∧
      ¬CFlat (RH.mapSignature (A.complexEmbedding phi) q) := by
  by_contra! noSmaller
  apply bad
  apply character_of_lower phi F bells c hc rmActual f actual hn even
  intro m hm q hq
  exact noSmaller m q hm hq

include bells hc rmActual in
theorem small_or_odd {n : ℕ} (f : Signature K n) (actual : Gadget.Realizes F .disequality f)
    (bad : ¬CFlat (RH.mapSignature (A.complexEmbedding phi) f)) :
    ∃m : ℕ,∃q : Signature K m,(m≤8 ∨ _root_.Odd m) ∧ Gadget.Realizes F .disequality q ∧
      ¬CFlat (RH.mapSignature (A.complexEmbedding phi) q) := by
  classical
  have aux : ∀k : ℕ,∀q : Signature K k,Gadget.Realizes F .disequality q→
      ¬CFlat (RH.mapSignature (A.complexEmbedding phi) q)→
      ∃m : ℕ,∃g : Signature K m,(m≤8 ∨ _root_.Odd m) ∧ Gadget.Realizes F .disequality g ∧
        ¬CFlat (RH.mapSignature (A.complexEmbedding phi) g) := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro q actualQ badQ
      by_cases small : k≤8
      · exact ⟨k,q,Or.inl small,actualQ,badQ⟩
      rcases Nat.even_or_odd k with even|odd
      · obtain ⟨t,ht⟩ : ∃t : ℕ,k=t+2 := ⟨k-2,by omega⟩
        subst k
        have hn : 10≤t+2 := by obtain ⟨j,hj⟩ := even;omega
        obtain ⟨m,g,hm,actualG,badG⟩ := smaller_noncharacter phi F bells c hc rmActual q actualQ hn even badQ
        exact ih m hm g actualG badG
      · exact ⟨k,q,Or.inr odd,actualQ,badQ⟩
  exact aux n f actual bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinCharacterDescent
end
