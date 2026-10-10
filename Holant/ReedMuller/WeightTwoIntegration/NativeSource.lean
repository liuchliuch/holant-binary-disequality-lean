import Holant.ReedMuller.WeightTwoIntegration.Structure
import Holant.ReedMuller.WeightTwoIntegration.Source
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalNativeI

/-! Full source7.9 with precisely the physical retained-resource boundary:
original q and literal I are signatures; X links are actual native edges.
No closure of the signature family under ports or analytic bases is assumed. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false

/-- The complete source alternative from actual fixed-representative cards.
The native realization uses at most seven vertices and nine native-X edges,
with exactly two original q labels and every other vertex literal I. -/
 theorem source_native_weight_two_integration {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (family : SignatureFamily ℂ)
    (hI : (⟨2,literalI⟩ : AnySignature ℂ)∈family)
    (q : Signature ℂ (n+2)) (hq : q≠0) (hqmem : (⟨n+2,q⟩ : AnySignature ℂ)∈family)
    (hn : 6≤n+2) (hdeck : CanonicalMatchingDeck G R q)
    (hW : ∃u v,(weightGraph (walsh q)).Adj u v) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor q ∨ TwoCopyEven4 family q := by
  rcases source_weight_two_structure hG hspan R q hq hn hdeck hW with hf | hE
  · exact Or.inl hf
  · have hn4 : n=4 := by have he:=hE.arity; omega
    subst n
    obtain ⟨d,p,c,hc,he⟩ := hE
    exact Or.inr ⟨rfl,exceptional_nativeI_two_copy_even4 d q hqmem hI p c hc he⟩

 theorem source_native_prime_weight_graph_empty {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (family : SignatureFamily ℂ)
    (hI : (⟨2,literalI⟩ : AnySignature ℂ)∈family)
    (q : Signature ℂ (n+2)) (hq : q≠0) (hqmem : (⟨n+2,q⟩ : AnySignature ℂ)∈family)
    (hn : 8≤n+2) (hdeck : CanonicalMatchingDeck G R q)
    (hprime : ¬Pauli.ExoticKlein.Fiber.HasProperTensorFactor q) : weightGraph (walsh q)=⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj,iff_false]
  intro h
  rcases source_native_weight_two_integration hG hspan R family hI q hq hqmem
    (by omega) hdeck ⟨u,v,h⟩ with hf | hE
  · exact hprime hf
  · have hh:=hE.1
    omega

 theorem source_native_factor_or_even4 {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (R : FixedIXRepresentatives) (family : SignatureFamily ℂ)
    (hI : (⟨2,literalI⟩ : AnySignature ℂ)∈family)
    (q : Signature ℂ (n+2)) (hq : q≠0) (hqmem : (⟨n+2,q⟩ : AnySignature ℂ)∈family)
    (hn : 6≤n+2) (hdeck : CanonicalMatchingDeck G R q)
    (hW : ∃u v,(weightGraph (walsh q)).Adj u v) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor q ∨
      (n+2=6 ∧ Gadget.RealizesUpTo family .disequality even4) := by
  rcases source_native_weight_two_integration hG hspan R family hI q hq hqmem hn hdeck hW with hf | hE
  · exact Or.inl hf
  · exact Or.inr ⟨hE.1,hE.realizes⟩

end Holant.ReedMuller.WeightTwoIntegration
