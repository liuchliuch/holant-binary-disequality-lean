import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2ReedMuller
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2CodeAffine
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SixPortPrime

/-! Closed local C2 stable-prime classification over the original field.
A proper even prime is quaternary or an eight-port affine Reed--Muller tensor.
The latter conclusion includes its genuine algebraic affine presentation.
Whole-family quaternary consumption is a separate mathematical obligation. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeClassification
open Holant Holant.Tractable
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain Holant.Projective.BoundedTorsion
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000
set_option Elab.async false

variable {K : Type*} [Field K] [NumberField K]
variable (F : SignatureFamily K) (torsion : ResidualTorsion F)
variable (hI : RetainsIdentity F) (cardTwo : Nat.card (completeGroup F torsion)=2)
variable (phi : K →+* AlgebraicComplex)

include torsion hI cardTwo in
theorem current_eight_affine (f : Signature K 8)
    (prime : Prime (⟨8,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    Affine (RingHomRealization.mapSignature phi f) := by
  let psi : K →+* ℂ := (algebraicClosure ℚ ℂ).subtype.comp phi
  obtain ⟨e,c,a,hc,equation⟩ :=
    GlobalCloseCompletionC2ReedMuller.current_prime_exact_code F torsion hI cardTwo psi f prime stable
  have nonzero : RingHomRealization.mapSignature phi f≠0 := ((prime_mapSignature_iff phi _).mpr prime).1
  apply GlobalCloseCompletionC2CodeAffine.affine_of_code (RingHomRealization.mapSignature phi f) nonzero e a c hc
  intro x
  have h := equation x
  change ((phi (f x) : AlgebraicComplex) : ℂ)=_ at h ⊢
  by_cases hx : (fun p=>Holant.ReedMuller.FlatNetwork.boolEquiv (x (e p)))+a∈Holant.ReedMuller.CoefficientAtlas.code
  · simpa only [if_pos hx] using h
  · simpa only [if_neg hx] using h

include torsion hI cardTwo in
theorem current_prime_classification {m : ℕ} (f : Signature K (m+2))
    (proper : 2≤m) (even : Even (m+2))
    (prime : Prime (⟨m+2,f⟩ : AnySignature K))
    (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g) :
    m=2 ∨ (m=6 ∧ Affine (RingHomRealization.mapSignature phi f)) := by
  classical
  by_cases four : m=2
  · exact Or.inl four
  have six : 4≤m := by rcases even with ⟨k,hk⟩; omega
  let psi : K →+* ℂ := (algebraicClosure ℚ ℂ).subtype.comp phi
  by_cases hsix : m=4
  · subst m
    exact False.elim (GlobalCloseCompletionC2SixPortPrime.current_not_prime
      F torsion hI cardTwo psi f prime stable)
  have higher : 8≤m+2 := by rcases even with ⟨k,hk⟩; omega
  have size := (GlobalCloseCompletionC2HigherStructure.current_prime_reed_muller_support
    F torsion hI cardTwo psi f prime higher stable).1
  have hm : m=6 := by omega
  subst m
  exact Or.inr ⟨rfl,current_eight_affine F torsion hI cardTwo phi f prime stable⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2PrimeClassification
end
