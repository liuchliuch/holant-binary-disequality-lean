import Holant.Certificates.OctahedralSeparator.Interface

/-! Public operational bounds and the exact mixed-form routing clauses of
Lemma9.12/PropositionA.16, interpreted with correction M001. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- A literal native-X network with its initial pair vertex distinguished.
Every vertex is an actual permitted resource; after that initial pair, at
most four binary vertices remain. The original ancestor occurs exactly once. -/
def BoundedNativeRealization {n : ℕ} (f : Form) (h : Signature ℂ 6)
    (K : Native.Binary) (t : Signature ℂ n) : Prop :=
  ∃ N : Network ℂ n, ∃ initial : Fin N.shape.vertices,
    N.denote=t ∧
    (⟨N.shape.arity initial,N.vertex initial⟩ : AnySignature ℂ)=
      ⟨2,Native.binarySignature (Native.pairVertex K)⟩ ∧
    (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ markedResources f h) ∧
    (∀ e, N.edge e=Signature.disequality) ∧
    (Finset.univ.filter (fun v => N.shape.arity v=6)).card=1 ∧
    (Finset.univ.filter (fun v => v≠initial ∧ N.shape.arity v=2)).card≤4

theorem bounded_endpoint_network (j : Fin 48) (hj : ¬outsideRow j)
    (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) :
    BoundedNativeRealization (rowForm j) h K (complexTensor (endpointOutput j)) := by
  refine ⟨Native.orderedDressedNetwork p h K (fun a => complexMatrix (finalLegs j a)),(1 : Fin 6),?_,rfl,?_,?_,?_,?_⟩
  · rw [Native.orderedDressedNetwork_denote,hcard,← endpoint_physical j hj]
  · intro v
    fin_cases v
    · change (⟨6,(Native.orderedDressedNetwork p h K _).vertex (0 : Fin 6)⟩ : AnySignature ℂ) ∈ _
      rw [Native.orderedDressedNetwork_ancestor]
      exact markedResources_ancestor _ _
    · exact markedResources_binary _ _ _ (pairVertex_available hK)
    · exact markedResources_binary _ _ _ (legVertex_available (finalLegs_available j 0))
    · exact markedResources_binary _ _ _ (legVertex_available (finalLegs_available j 1))
    · exact markedResources_binary _ _ _ (legVertex_available (finalLegs_available j 2))
    · exact markedResources_binary _ _ _ (legVertex_available (finalLegs_available j 3))
  · intro e
    rfl
  · exact Native.orderedDressedNetwork_ancestor_vertices _ _ _ _
  · change (Finset.univ.filter (fun v : Fin 6 => v≠1 ∧ Native.dressedArity v=2)).card≤4
    decide

theorem bounded_outside_network (j : Fin 48) (hj : outsideRow j)
    (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) :
    BoundedNativeRealization (rowForm j) h K (Native.binarySignature (complexMatrix (outsideValues j))) := by
  refine ⟨Native.orderedSparseNetwork p h K (complexMatrix (correction (rowForm j)))
    (complexMatrix (correction (rowForm j))) (complexMatrix (closureKernel j)),(1 : Fin 5),?_,rfl,?_,?_,?_,?_⟩
  · rw [Native.orderedSparseNetwork_denote,hcard]
    have hc : ![Signature.equality,complexMatrix (correction (rowForm j)),
        Signature.equality,complexMatrix (correction (rowForm j))]=
        (fun a => complexMatrix (corrections (rowForm j) a)) := by
      funext a
      fin_cases a <;> simp [corrections,quaternionBasis,Q0] <;> rfl
    rw [hc,← outside_physical j hj]
    rfl
  · intro v
    fin_cases v
    · change (⟨6,(Native.orderedSparseNetwork p h K _ _ _).vertex (0 : Fin 5)⟩ : AnySignature ℂ) ∈ _
      rw [Native.orderedSparseNetwork_ancestor]
      exact markedResources_ancestor _ _
    · exact markedResources_binary _ _ _ (pairVertex_available hK)
    · exact markedResources_binary _ _ _ (legVertex_available (direction_correction _))
    · exact markedResources_binary _ _ _ (legVertex_available (direction_correction _))
    · exact markedResources_binary _ _ _ (pairVertex_available (closureKernel_available j))
  · intro e
    rfl
  · exact Native.orderedSparseNetwork_ancestor_vertices _ _ _ _ _ _
  · change (Finset.univ.filter (fun v : Fin 5 => v≠1 ∧ Native.sparseArity v=2)).card≤4
    decide

def EndpointExit (f : Form) (h : Signature ℂ 6) : Prop :=
  ∃ t : Signature ℂ 4, Gadget.Realizes (markedResources f h) .disequality t ∧
    TetrahedralOrientation.EndpointNondegenerateEightVertex t ∧ ∀ r : Fin 3, (flatten r t).rank=2
def OutsideExit (f : Form) (h : Signature ℂ 6) : Prop :=
  ∃ B : Native.Binary, Gadget.Realizes (markedResources f h) .disequality (Native.binarySignature B) ∧
    Matrix.det (Matrix.of B) ≠ 0 ∧ ¬Direction f (nativeTransfer B)

theorem normalized_outside_exit (f : Form) (frame : Fin 4) (order : Fin 6)
    (h : Signature ℂ 6) (hN : NormalizedCardMap f (fullImages frame order) h)
    (ho : outsideRow (regularRow f (frames frame (permutations order 0)))) : OutsideExit f h := by
  let j := regularRow f (frames frame (permutations order 0))
  have hcard : Signature.contract (complexMatrix (theta f firstKernel))
      (Tensor.reindex (Equiv.refl _) h)=complexTensor (coefficientCard (rowForm j) (rowBase j)) := by
    simpa only [j,regularRow_form,regularRow_base,Tensor.reindex_refl] using normalized_first_card f frame order h hN
  have hK : Direction (rowForm j) (Matrix.of (complexMatrix (theta f firstKernel))) := by
    change Direction (rowForm j) (complexMatrix (theta f firstKernel))
    simpa only [j,regularRow_form] using firstKernel_available f
  refine ⟨complexMatrix (outsideValues j),?_,outside_nonsingular j ho,?_⟩
  · simpa only [j,regularRow_form] using outside_realizes j ho h (Equiv.refl _) _ hK hcard
  · simpa only [j,regularRow_form] using outside_transfer_not_direction j ho

theorem dt_route_check : ∀ r : Fin 9,
    (¬outsideRow (regularRow 2 r) ↔ r=0 ∨ r=1 ∨ r=2) ∧
    (outsideRow (regularRow 2 r) ↔ 3≤r.val) := by decide
theorem td_route_check : ∀ r : Fin 9,
    (¬outsideRow (regularRow 3 r) ↔ r=0 ∨ r=1 ∨ r=2) ∧
    (outsideRow (regularRow 3 r) ↔ 3≤r.val) := by decide

/-- Source R0,R1,R3 are indices0,1,2 of the literal nine-entry dictionary. -/
theorem dt_R0_R1_R3_eight_vertex (frame : Fin 4) (order : Fin 6) (h : Signature ℂ 6)
    (hN : NormalizedCardMap 2 (fullImages frame order) h)
    (hr : frames frame (permutations order 0)=0 ∨ frames frame (permutations order 0)=1 ∨
      frames frame (permutations order 0)=2) : EndpointExit 2 h :=
  normalized_endpoint_exit 2 frame order h hN ((dt_route_check _).1.mpr hr)

theorem dt_other_six_outside (frame : Fin 4) (order : Fin 6) (h : Signature ℂ 6)
    (hN : NormalizedCardMap 2 (fullImages frame order) h)
    (hr : 3≤(frames frame (permutations order 0)).val) : OutsideExit 2 h :=
  normalized_outside_exit 2 frame order h hN ((dt_route_check _).2.mpr hr)

theorem td_R0_R3_eight_vertex (frame : Fin 4) (order : Fin 6) (h : Signature ℂ 6)
    (hN : NormalizedCardMap 3 (fullImages frame order) h)
    (hr : frames frame (permutations order 0)=0 ∨ frames frame (permutations order 0)=2) : EndpointExit 3 h := by
  apply normalized_endpoint_exit 3 frame order h hN
  apply (td_route_check _).1.mpr
  rcases hr with hr | hr
  · exact Or.inl hr
  · exact Or.inr (Or.inr hr)

theorem td_other_six_outside (frame : Fin 4) (order : Fin 6) (h : Signature ℂ 6)
    (hN : NormalizedCardMap 3 (fullImages frame order) h)
    (hr : 3≤(frames frame (permutations order 0)).val) : OutsideExit 3 h :=
  normalized_outside_exit 3 frame order h hN ((td_route_check _).2.mpr hr)

theorem td_R1_pure_equality (frame : Fin 4) (order : Fin 6) (h : Signature ℂ 6)
    (hN : NormalizedCardMap 3 (fullImages frame order) h)
    (hr : frames frame (permutations order 0)=1) :
    Gadget.Realizes (markedResources 3 h) .disequality
      (embed (coeff (3/8) (1/4) 0 0) • complexEq4) := by
  have hcard : Signature.contract (complexMatrix (theta 3 firstKernel))
      (Tensor.reindex (Equiv.refl _) h)=complexTensor (coefficientCard (rowForm 34) (rowBase 34)) := by
    change Signature.contract (complexMatrix (theta 3 firstKernel)) (Tensor.reindex (Equiv.refl _) h)=
      complexTensor (coefficientCard 3 (Fin.castAdd 6 (1 : Fin 9)))
    simpa only [hr,Tensor.reindex_refl] using normalized_first_card 3 frame order h hN
  have hK : Direction (rowForm 34) (Matrix.of (complexMatrix (theta 3 firstKernel))) := firstKernel_available 3
  rw [← equality_output]
  exact endpoint_realizes 34 (by decide) h (Equiv.refl _) _ hK hcard

end
end Holant.Certificates.OctahedralSeparator
