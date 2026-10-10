import Holant.ReedMuller.WeightTwoIntegration.CanonicalSix
import Holant.ReedMuller.WeightTwoIntegration.ThreeProduct
import Holant.ReedMuller.WeightTwoIntegration.ExceptionalOriginalPorts

/-! Scaled-I/X-resource version of Lemma7.9: a nonempty original weight-two graph gives either
an exact proper tensor factor or the actual constant-size two-copy Even4
network. The fixed physical representatives, original f labels, analytic
Walsh normalization and all nonzero physical multipliers are retained.
The literal-I/native-X source specialization is supplied separately. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
open Holant.ReedMuller.CoefficientAtlas Holant.Certificates.MatchingContractionClosure
set_option backward.isDefEq.respectTransparency false

 def ExceptionalBinaries.representatives {family : SignatureFamily ℂ} (B : ExceptionalBinaries family) :
    FixedIXRepresentatives where
  kernel minus := B.scale minus • actualKernel minus
  scale := B.scale
  scale_ne_zero := B.nonzero
  exact _ := rfl

/-- Literal physical witness, with exactly two original six-port labels.
The possible seventh vertex is the actual parity-coset correcting binary. -/
 def TwoCopyEven4 {n : ℕ} (family : SignatureFamily ℂ) (q : Signature ℂ n) : Prop :=
  n=6 ∧ ∃N : Network ℂ 4,∃s : ℂ,s≠0 ∧ N.denote=(fun x=>s*even4 x) ∧
    N.shape.vertices≤7 ∧ N.shape.edges≤9 ∧
    Fintype.card {v : Fin N.shape.vertices // N.shape.arity v=6}=2 ∧
    (∀v,N.shape.arity v=6 → HEq (N.vertex v) q) ∧
    (∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ)∈family) ∧
    (∀e,N.edge e=Signature.disequality)

 theorem TwoCopyEven4.realizes {n : ℕ} {family : SignatureFamily ℂ} {q : Signature ℂ n}
    (h : TwoCopyEven4 family q) : Gadget.RealizesUpTo family .disequality even4 := by
  obtain ⟨_,N,s,hs,hden,_,_,_,_,hv,he⟩ := h
  refine ⟨s,hs,?_⟩
  rw [←hden]
  exact Gadget.realizes_network N family .disequality hv he

/-- Source7.9 on the actual fixed canonical one-copy deck. Perfection of W,
full logical support, diagonal-slice simplicity, the exceptional coefficient
table and all three square relations are conclusions of those actual cards. -/
 theorem source_weight_two_integration {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (family : SignatureFamily ℂ) (B : ExceptionalBinaries family)
    (q : Signature ℂ (n+2)) (hq : q≠0) (hqmem : (⟨n+2,q⟩ : AnySignature ℂ)∈family)
    (hn : 6≤n+2) (hdeck : CanonicalMatchingDeck G B.representatives q)
    (hW : ∃u v,(weightGraph (walsh q)).Adj u v) :
    Pauli.ExoticKlein.Fiber.HasProperTensorFactor q ∨ TwoCopyEven4 family q := by
  have ha := actualMatchingDeck_of_canonical B.representatives q hdeck
  have H := source_matching_consistency hG hspan B.representatives q hq hn hdeck
  have hd := actual_equality_deck hG hspan B.representatives q ha
  have hw := actual_weighted_deck hG hspan B.representatives q ha
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
      have h0 := C.logical_nonzero (by norm_num) H hd hn (fun _=>false)
      have hphys := C.canonical_physical q hc H (fun i=>(rho i:ℂ)) kap he
      exact Or.inr ⟨rfl,exceptional_original_two_copy_even4 d B q hqmem
        (C.canonicalOrder hc).symm (C.logical (fun _=>false)) h0 hphys⟩

/-- Consequently an actual prime of arity at least eight has no weight-two
edge. This uses literal tensor primeness, with no protocol transition claim. -/
 theorem source_prime_weight_graph_empty {n : ℕ} {G : Set (Binary (K := ℂ))}
    (hG : ProjectiveMatrixGroup G)
    (hspan : ∀T∈G,∃α β : ℂ,T=fun a b=>α*Signature.equality a b+β*Signature.disequality a b)
    (family : SignatureFamily ℂ) (B : ExceptionalBinaries family)
    (q : Signature ℂ (n+2)) (hq : q≠0) (hqmem : (⟨n+2,q⟩ : AnySignature ℂ)∈family)
    (hn : 8≤n+2) (hdeck : CanonicalMatchingDeck G B.representatives q)
    (hprime : ¬Pauli.ExoticKlein.Fiber.HasProperTensorFactor q) : weightGraph (walsh q)=⊥ := by
  ext u v
  simp only [SimpleGraph.bot_adj,iff_false]
  intro h
  rcases source_weight_two_integration hG hspan family B q hq hqmem (by omega) hdeck ⟨u,v,h⟩ with hf | hE
  · exact hprime hf
  · have hh := hE.1
    omega

end Holant.ReedMuller.WeightTwoIntegration
