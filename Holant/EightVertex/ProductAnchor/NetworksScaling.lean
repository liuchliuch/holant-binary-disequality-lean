import Holant.EightVertex.ProductAnchor.Networks
import Holant.NetworkAlgebra

/-! Exact scalar propagation for the normalized labels η Fs from Lemma 4.2.
The raw output keeps one η per actual vertex. -/
namespace Holant.EightVertex.ProductAnchor
open Holant
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [CommRing K]

def uniformlyScaleNetwork (η : K) (N : Network K 4) : Network K 4 :=
  N.scaleVertices (fun _ => η)

/-- The same physical graph, each genuine vertex labelled by η Fs. -/
def scaledNetwork (s : Word) (η : K) : Network K 4 :=
  uniformlyScaleNetwork η (normalizedNetwork s)

def scaledOutput (s : Word) (η : K) : K :=
  η ^ (normalizedNetwork (K := K) s).shape.vertices * outputScalar s

theorem scaledNetwork_denote (s : Word) (η : K) :
    (scaledNetwork s η).denote = fun x => scaledOutput s η * equalityFour x := by
  funext x
  rw [scaledNetwork,uniformlyScaleNetwork,Network.denote_scaleVertices,normalizedNetwork_denote]
  simp [scaledOutput,mul_assoc]

theorem scaledNetwork_vertices_le_two (s : Word) (η : K) :
    (scaledNetwork s η).shape.vertices ≤ 2 := normalizedNetwork_vertices_le_two s

theorem scaledNetwork_labels (s : Word) (η : K) :
    LabelsAre (scaledNetwork s η) (fun x => η * normalized s x) := by
  unfold scaledNetwork normalizedNetwork
  split <;> intro v <;> rfl

theorem scaledNetwork_edges (s : Word) (η : K) (e : Fin (scaledNetwork s η).shape.edges) :
    (scaledNetwork s η).edge e = Signature.equality := normalizedNetwork_edges s e

def scaledOpenNetwork (s : Word) (η : K) : OpenNetwork K 4 :=
  (scaledNetwork s η).asOpen (fun _ => .equality)

theorem scaledOpenNetwork_raw (s : Word) (η : K) :
    (scaledOpenNetwork s η).raw = fun x => scaledOutput s η * equalityFour x := by
  rw [scaledOpenNetwork,Network.raw_asOpen]
  · exact scaledNetwork_denote s η
  · intro e
    exact (scaledNetwork_edges s η e).symm

theorem scaled_realizes (s : Word) (η : K) :
    Gadget.Realizes ({⟨4,fun x => η * normalized s x⟩} : SignatureFamily K) .equality
      (fun x => scaledOutput s η * equalityFour x) := by
  rw [←scaledNetwork_denote]
  apply Gadget.realizes_network
  · intro v
    rw [scaledNetwork_labels s η v]
    exact Set.mem_singleton _
  · exact scaledNetwork_edges s η

theorem scaledOutput_ne_zero [Nontrivial K] [NoZeroDivisors K] (s : Word)
    (η : K) (hη : η ≠ 0) : scaledOutput s η ≠ 0 :=
  mul_ne_zero (pow_ne_zero _ hη) (outputScalar_ne_zero s)

theorem scaled_realizesUpTo [Nontrivial K] [NoZeroDivisors K] (s : Word)
    (η : K) (hη : η ≠ 0) :
    Gadget.RealizesUpTo ({⟨4,fun x => η * normalized s x⟩} : SignatureFamily K)
      .equality equalityFour :=
  ⟨scaledOutput s η,scaledOutput_ne_zero s η hη,scaled_realizes s η⟩

end Holant.EightVertex.ProductAnchor
