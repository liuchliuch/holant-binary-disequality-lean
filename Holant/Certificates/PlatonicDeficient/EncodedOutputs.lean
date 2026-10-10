import Holant.Certificates.PlatonicDeficient.NormalizedOutputs
import Holant.Platonic.RainbowLocalization.EncodedReduction

/-! Encoded adjoining reductions for the actual normalized deficient outputs.
The proof labels the literal ordinary graph with a fixed finite algebraic
retained family; it does not convert an abstract Gadget.Realizes witness. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Algebraic
open Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.Platonic.RainbowLocalization.Physical
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

variable {s : ℕ} {arity : ℕ → ℕ}
variable (signatures : (i : Fin s) → Signature ℂ (arity i.val))
variable (halg : ∀ i x, IsAlgebraic ℚ (signatures i x))

/-- Every vertex of this ordinary graph is a literal retained signature.
In particular, port reordering does not replace the stored ancestor label. -/
theorem ordered_dressed_retained_vertices (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Native.Binary) (L : Fin 4 → Native.Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : ∀ j, (⟨2,Native.binarySignature (Native.legVertex (L j))⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    ∀ v, (⟨(Native.orderedDressedNetwork p h K L).shape.arity v,
      (Native.orderedDressedNetwork p h K L).vertex v⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures := by
  intro v
  fin_cases v
  · change (⟨6,(Native.orderedDressedNetwork p h K L).vertex (0 : Fin 6)⟩ : AnySignature ℂ) ∈ _
    rw [Native.orderedDressedNetwork_ancestor]
    exact hh
  · exact hK
  · exact hL 0
  · exact hL 1
  · exact hL 2
  · exact hL 3

/-- Literal ordinary macro, exact coefficient labels, and the encoded
polynomial Boolean oracle reduction supplied by the retained-family API. -/
theorem ordered_dressed_encoded_adjoin (p : Equiv.Perm (Fin 6))
    (h : Signature ℂ 6) (K : Native.Binary) (L : Fin 4 → Native.Binary)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex K)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : ∀ j, (⟨2,Native.binarySignature (Native.legVertex (L j))⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedNativeAdjoin signatures halg
      (Signature.coordinateAction L (Signature.contract K (Tensor.reindex p h))) := by
  have he := retained_network_encoded_adjoin signatures halg
    (Native.orderedDressedNetwork p h K L)
    (ordered_dressed_retained_vertices signatures p h K L hh hK hL) (fun _ => rfl)
  rwa [Native.orderedDressedNetwork_denote] at he

/-- The standard I contraction needs exactly the literal pair-I and identity
leg vertices; its retained-family assumption does not quantify over scalings. -/
theorem output_encoded_adjoin (p : Fin 6)
    (hh : (⟨6,ancestor p⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : (⟨2,Native.binarySignature (Native.legVertex Signature.equality)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedNativeAdjoin signatures halg (output p) := by
  rw [output_contract]
  have he := ordered_dressed_encoded_adjoin signatures halg
    (TetrahedralDeck.portOrder 1).symm (ancestor p) Q0 (fun _ => Signature.equality)
    hh hK (fun _ => hL)
  simpa only [Signature.coordinateAction_equality] using he

/-- The actual O′ ordinary graph contains only the original ancestor, I pair
vertex, and literal current-group correction legs. H and H⁻¹ are not labels. -/
theorem primeOutput_encoded_adjoin (p : Fin 6)
    (hh : (⟨6,primeAncestor p⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : ∀ j : Fin 4,
      (⟨2,Native.binarySignature (Native.legVertex (complexMatrix (corrections 1 j)))⟩ :
        AnySignature ℂ) ∈ indexedRetainedFamily arity signatures) :
    EncodedNativeAdjoin signatures halg (primeOutput p) := by
  rw [primeOutput_actual]
  exact ordered_dressed_encoded_adjoin signatures halg
    (TetrahedralDeck.portOrder 1).symm (primeAncestor p) Q0
    (fun j => complexMatrix (corrections 1 j)) hh hK hL

def EncodedStandardOutput (h : Signature ℂ 6) : Prop :=
  ∃ p : Fin 6, h = ancestor p ∧
    EncodedNativeAdjoin signatures halg (output p) ∧
    (support (output p)).card = 10 ∧
    ∀ r : Fin 3, (flatten r (output p)).rank = 3

theorem standard_deficient_encoded_of_output (g : PlatonicModel) (h : Signature ℂ 6)
    (hout : StandardDeficientOutput g h)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : (⟨2,Native.binarySignature (Native.legVertex Signature.equality)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedStandardOutput signatures halg h := by
  obtain ⟨p,hp,_,_,hs,hr⟩ := hout
  refine ⟨p,hp,?_,hs,hr⟩
  apply output_encoded_adjoin signatures halg p _ hK hL
  rwa [←hp]

theorem tetrahedral_deficient_encoded_output (h : Signature ℂ 6)
    (hn : TetrahedralBridge.Normalized (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : TetrahedralBridge.mapRank (PlatonicBridgeInterface.Octahedral.actualMap h) < 4)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : (⟨2,Native.binarySignature (Native.legVertex Signature.equality)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedStandardOutput signatures halg h :=
  standard_deficient_encoded_of_output signatures halg .tetrahedral h
    (tetrahedral_deficient_output h hn hr) hh hK hL

theorem icosahedral_deficient_encoded_output (h : Signature ℂ 6)
    (hn : IcosahedralSeparator.Normalized (IcosahedralSeparator.actualMap h))
    (hr : IcosahedralSeparator.mapRank (IcosahedralSeparator.actualMap h) < 4)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : (⟨2,Native.binarySignature (Native.legVertex Signature.equality)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedStandardOutput signatures halg h :=
  standard_deficient_encoded_of_output signatures halg .icosahedral h
    (icosahedral_deficient_output h hn hr) hh hK hL

theorem octahedral_deficient_encoded_output (h : Signature ℂ 6)
    (hn : PlatonicBridgeInterface.Octahedral.SourceHypotheses 0
      (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : PlatonicBridgeInterface.Octahedral.mapRank
      (PlatonicBridgeInterface.Octahedral.actualMap h) < 4)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : (⟨2,Native.binarySignature (Native.legVertex Signature.equality)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures) :
    EncodedStandardOutput signatures halg h :=
  standard_deficient_encoded_of_output signatures halg .octahedral h
    (octahedral_deficient_output h hn hr) hh hK hL

theorem prime_deficient_encoded_output (h : Signature ℂ 6)
    (hn : PlatonicBridgeInterface.Octahedral.SourceHypotheses 1
      (PlatonicBridgeInterface.Octahedral.actualMap h))
    (hr : PlatonicBridgeInterface.Octahedral.mapRank
      (PlatonicBridgeInterface.Octahedral.actualMap h) < 4)
    (hh : (⟨6,h⟩ : AnySignature ℂ) ∈ indexedRetainedFamily arity signatures)
    (hK : (⟨2,Native.binarySignature (Native.pairVertex Q0)⟩ : AnySignature ℂ) ∈
      indexedRetainedFamily arity signatures)
    (hL : ∀ j : Fin 4,
      (⟨2,Native.binarySignature (Native.legVertex (complexMatrix (corrections 1 j)))⟩ :
        AnySignature ℂ) ∈ indexedRetainedFamily arity signatures) :
    ∃ p : Fin 6, h = primeAncestor p ∧
      EncodedNativeAdjoin signatures halg (primeOutput p) ∧
      ∀ r : Fin 3, (flatten r (primeOutput p)).rank = 3 := by
  obtain ⟨p,hp,_,hR⟩ := prime_deficient_output h hn hr
  refine ⟨p,hp,?_,hR⟩
  apply primeOutput_encoded_adjoin signatures halg p _ hK hL
  rwa [←hp]

end
end Holant.Certificates.PlatonicDeficient
