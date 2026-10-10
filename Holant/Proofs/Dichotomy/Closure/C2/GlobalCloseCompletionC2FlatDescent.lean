import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RadonCards
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMLocalization

/-! Actual lower-output descent for the entire RM-generated family. The
lower-output class test is discharged internally by classical case analysis:
a nonflat even actual row of arity at least ten has a smaller actual nonflat
row. No caller-supplied classification, deck stability, or closure backend is
an input. The same original coefficient field and RM multiplier are retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatDescent
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffineRadon Holant.ReedMuller.TwoChart
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
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

theorem affine_of_flatOrZero {n : ℕ} (f : Signature AlgebraicComplex n)
    (h : FlatOrZero (fun x=>(f x:ℂ))) : Affine f := by
  rcases exists_flat_chart f h with rfl|⟨C,_zero,rfl⟩
  · exact affine_zero n
  · exact affine_coset_character C.scalar C.shift C.direction C.character

variable {K : Type*} [Field K] [CharZero K]
variable (phi : K→+*AlgebraicComplex) (F : SignatureFamily K)
variable (hI : (⟨2,B.identity⟩ : AnySignature K)∈F)
variable (c : K) (hc : c≠0) (actualRM : Gadget.Realizes F .disequality (c • R.rm))

include hI hc actualRM in
theorem flat_of_lower {n : ℕ} (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)
    (hn : 10≤n+2) (even : Even (n+2))
    (lower : ∀m : ℕ,m<n+2→∀q : Signature K m,Gadget.Realizes F .disequality q→
      FlatOrZero (RH.mapSignature (A.complexEmbedding phi) q)) :
    FlatOrZero (RH.mapSignature (A.complexEmbedding phi) f) := by
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
  have cards : FlatRadonCards (fun y=>(g (wordVector y):ℂ)) := by
    intro v hv
    obtain ⟨frame,direction,outputs⟩ := GlobalCloseCompletionC2RadonCards.actual_cards phi F hI c hc actualRM f actual v hv
    refine ⟨frame,direction,?_⟩
    intro ε
    obtain ⟨q,actualQ,flatQ⟩ := outputs ε
    exact flatQ (lower n (by omega) q actualQ)
  have affine : Affine g := by
    by_contra bad
    obtain ⟨m,q,bound,_positive,_nonzero,actualQ,badK⟩ := GlobalCloseCompletionC2RMLocalization.from_flat_cards
      phi F hI c hc actualRM f actual hn even cards bad
    have flatQ := lower m (by omega) q actualQ
    have affineQ := affine_of_flatOrZero (RH.mapSignature phi q) flatQ
    exact badK (GlobalCloseCompletionC2KAffine.sourceK_affine _ affineQ)
  exact Or.inr (source_affine_to_flat_radon_even (by omega) even g affine nonzero cards)

include hI hc actualRM in
theorem smaller_nonflat {n : ℕ} (f : Signature K (n+2)) (actual : Gadget.Realizes F .disequality f)
    (hn : 10≤n+2) (even : Even (n+2))
    (bad : ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) f)) :
    ∃m : ℕ,∃q : Signature K m,m<n+2 ∧ Gadget.Realizes F .disequality q ∧
      ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) q) := by
  by_contra! noSmaller
  apply bad
  apply flat_of_lower phi F hI c hc actualRM f actual hn even
  intro m hm q hq
  exact noSmaller m q hm hq

include hI hc actualRM in
theorem small_or_odd {n : ℕ} (f : Signature K n) (actual : Gadget.Realizes F .disequality f)
    (bad : ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) f)) :
    ∃m : ℕ,∃q : Signature K m,(m≤8 ∨ Odd m) ∧ Gadget.Realizes F .disequality q ∧
      ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) q) := by
  classical
  have aux : ∀k : ℕ,∀q : Signature K k,Gadget.Realizes F .disequality q→
      ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) q)→
      ∃m : ℕ,∃g : Signature K m,(m≤8 ∨ Odd m) ∧ Gadget.Realizes F .disequality g ∧
        ¬FlatOrZero (RH.mapSignature (A.complexEmbedding phi) g) := by
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
        obtain ⟨m,g,hm,actualG,badG⟩ := smaller_nonflat phi F hI c hc actualRM q actualQ hn even badQ
        exact ih m hm g actualG badG
      · exact ⟨k,q,Or.inr odd,actualQ,badQ⟩
  exact aux n f actual bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2FlatDescent
end
