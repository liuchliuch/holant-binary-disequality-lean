import Holant.Certificates.MatchingContractionClosure.NativeCollection
import Mathlib.Basic.Complex.Basic

/-! Full manuscript Lemma9.10, with arbitrary disjoint original-port
collections, closed components, zero inputs/outputs, and actual native-X graphs. -/
namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- Lemma9.10. A saturated representative set presents G≤PGL2. Its inverse
law forces actual nonsingularity; reversal stability and X-membership are
exactly the remaining source assumptions. -/
theorem platonic_matching_contraction_closure
    (G : Set (Binary (K := ℂ))) (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := ℂ)) ∈ G) (hrev : ReversalStable G)
    {P Q E : Type*} [DecidableEq P] [Fintype E] [DecidableEq E]
    (p : CollectionPorts P Q E) (C : E → Binary (K := ℂ)) (F : Tensor ℂ P)
    (hC : ∀ e, SafeBinary G (C e)) (hF : MatchingOrZero G F) :
    contractCollection p C F=0 ∨ ∃ M : Presentation ℂ Q,
      contractCollection p C F=M.tensor ∧ M.scalar≠0 ∧
      ∀ e, Matrix.det (M.matrix e)≠0 ∧ transfer (M.matrix e) ∈ G :=
  contractCollection_factorization hG hX hrev p C F hC hF

variable {K E : Type*} [Field K] [Fintype E] [DecidableEq E] {m n : ℕ}

def collectionResources (F : Signature K m) (C : E → Binary (K := K)) : SignatureFamily K :=
  {s | s=⟨m,F⟩ ∨ ∃ e : E, s=⟨2,binarySignature (nativePair (C e))⟩}

theorem nativeCollection_realizes (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) :
    Gadget.Realizes (collectionResources F C) .disequality (contractCollection p C F) := by
  have hv : ∀ v : Option E,
      (⟨(nativeCollectionFinite p C F).arity v,(nativeCollectionFinite p C F).vertex v⟩ : AnySignature K)
        ∈ collectionResources F C := by
    intro v
    cases v with
    | none => exact Or.inl rfl
    | some e => exact Or.inr ⟨e,rfl⟩
  have hr := Gadget.realizes_network (nativeCollectionNetwork p C F) (collectionResources F C) .disequality
    (by intro v; exact hv ((Fintype.equivFin (Option E)).symm v))
    (by intro e; rfl)
  rwa [nativeCollection_denote] at hr

/-- The graph uses one original tensor and one actual group binary per closed
pair, with two native-X edges per pair and no factor introduced as a resource. -/
theorem physical_matching_contraction_closure (G : Set (Binary (K := K)))
    (hG : ProjectiveMatrixGroup G) (hX : (X : Binary (K := K)) ∈ G) (hrev : ReversalStable G)
    (p : CollectionPorts (Fin m) (Fin n) E) (C : E → Binary (K := K)) (F : Signature K m)
    (hC : ∀ e, SafeBinary G (C e)) (hF : MatchingOrZero G F) :
    Gadget.Realizes (collectionResources F C) .disequality (contractCollection p C F) ∧
    (∀ e, SafeBinary G (nativePair (C e))) ∧
    (nativeCollectionNetwork p C F).shape.vertices=Fintype.card E+1 ∧
    (nativeCollectionNetwork p C F).shape.edges=2*Fintype.card E ∧
    ((nativeCollectionNetwork p C F).denote=0 ∨ ∃ M : Presentation K (Fin n),
      (nativeCollectionNetwork p C F).denote=M.tensor ∧ M.scalar≠0 ∧
      ∀ e, Matrix.det (M.matrix e)≠0 ∧ transfer (M.matrix e) ∈ G) := by
  refine ⟨nativeCollection_realizes p C F,fun e => nativePair_safe hG hX (hC e),
    nativeCollection_vertices p C F,nativeCollection_edges p C F,?_⟩
  rw [nativeCollection_denote]
  exact contractCollection_factorization hG hX hrev p C F hC hF

end
end Holant.Certificates.MatchingContractionClosure
