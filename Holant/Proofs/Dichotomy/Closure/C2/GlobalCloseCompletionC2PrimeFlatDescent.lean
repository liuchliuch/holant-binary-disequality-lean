import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatDescent
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2FlatMatching
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2RMFlat
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortPrime

/-! The remaining low-arity actual nonflat primes have smaller actual bad
cards. Lower flatness gives literal original-field matching cards internally;
6-port prime exclusion and 8-port RM flatness then close the no-descent case.
Together with the genuine Radon source this covers every even prime arity≥6. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeFlatDescent
open Holant Holant.Tractable Holant.LocalDrafts.MainChain
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.Projective.BoundedTorsion
namespace A
export GlobalCloseCompletionC2RadonActual (complexEmbedding)
end A
namespace B
export GlobalCloseCompletionC2BitTranslateActual (identity)
end B
namespace R
export GlobalCloseCompletionC2RMActual (rm)
end R
namespace RH
export RingHomRealization (mapSignature)
end RH
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type*} [Field K] [NumberField K] {m : ℕ}
variable (F : SignatureFamily K) (torsion : ResidualTorsion F) (hI : RetainsIdentity F)
variable (cardTwo : Nat.card (completeGroup F torsion)=2) (phi : K→+*ℂ)

include torsion hI cardTwo in
theorem low_card (f : Signature K (m+2)) (actual : Gadget.Realizes F .disequality f)
    (prime : Prime (⟨m+2,f⟩ : AnySignature K)) (six : 6≤m+2) (small : m+2≤8) (even : Even (m+2))
    (bad : ¬FlatOrZero (RH.mapSignature phi f)) :
    ∃q : Signature K m,Gadget.Realizes F .disequality q ∧ ¬FlatOrZero (RH.mapSignature phi q) := by
  by_contra! lower
  have stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g := by
    intro g member
    rcases member with rfl|⟨key,rfl⟩
    · exact Or.inl rfl
    · exact GlobalCloseCompletionC2FlatMatching.matching F torsion hI phi _ (by omega)
        (lower _ (rawCard_realizes_exact F torsion hI (by norm_num) f actual key))
  by_cases hsix : m=4
  · subst m
    exact GlobalCloseCompletionC2SixPortPrime.current_not_prime F torsion hI cardTwo phi f prime stable
  have height : m=6 := by obtain ⟨k,hk⟩ := even;omega
  subst m
  exact bad (Or.inr (GlobalCloseCompletionC2RMFlat.current_flat F torsion hI cardTwo phi f prime stable))

variable (psi : K→+*AlgebraicComplex) (c : K) (hc : c≠0)
variable (actualRM : Gadget.Realizes F .disequality (c • R.rm))

include torsion hI cardTwo hc actualRM in
theorem smaller (f : Signature K (m+2)) (actual : Gadget.Realizes F .disequality f)
    (prime : Prime (⟨m+2,f⟩ : AnySignature K)) (six : 6≤m+2) (even : Even (m+2))
    (bad : ¬FlatOrZero (RH.mapSignature (A.complexEmbedding psi) f)) :
    ∃n : ℕ,∃q : Signature K n,n<m+2 ∧ Gadget.Realizes F .disequality q ∧
      ¬FlatOrZero (RH.mapSignature (A.complexEmbedding psi) q) := by
  by_cases small : m+2≤8
  · obtain ⟨q,actualQ,badQ⟩ := low_card F torsion hI cardTwo (A.complexEmbedding psi) f actual prime six small even bad
    exact ⟨m,q,by omega,actualQ,badQ⟩
  have hn : 10≤m+2 := by obtain ⟨k,hk⟩ := even;omega
  exact GlobalCloseCompletionC2FlatDescent.smaller_nonflat psi F hI c hc actualRM f actual hn even bad


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeFlatDescent
end
