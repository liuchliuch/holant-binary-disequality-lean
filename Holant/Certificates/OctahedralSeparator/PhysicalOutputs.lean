import Holant.Certificates.OctahedralSeparator.OutputSemantics
import Holant.Certificates.OctahedralSeparator.NativeOrder

namespace Holant.Certificates.OctahedralSeparator
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The original ancestor and all actual binaries whose native-X transfer is
in the current complete marked group. No similarity is added as a resource. -/
def markedResources (f : Form) (h : Signature ℂ 6) : SignatureFamily ℂ :=
  {s | s=⟨6,h⟩ ∨ ∃ U : Native.Binary, s=⟨2,Native.binarySignature U⟩ ∧ Direction f (nativeTransfer U)}

theorem markedResources_ancestor (f : Form) (h : Signature ℂ 6) :
    (⟨6,h⟩ : AnySignature ℂ) ∈ markedResources f h := Or.inl rfl

theorem markedResources_binary (f : Form) (h : Signature ℂ 6) (U : Native.Binary)
    (hU : Direction f (nativeTransfer U)) :
    (⟨2,Native.binarySignature U⟩ : AnySignature ℂ) ∈ markedResources f h :=
  Or.inr ⟨U,rfl,hU⟩

theorem endpoint_realizes (j : Fin 48) (hj : ¬outsideRow j)
    (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) :
    Gadget.Realizes (markedResources (rowForm j) h) .disequality (complexTensor (endpointOutput j)) := by
  rw [endpoint_physical j hj,← hcard]
  apply Native.ordered_dressed_realizes_of_mem
  · exact markedResources_ancestor _ _
  · apply markedResources_binary
    exact pairVertex_available hK
  · intro a
    apply markedResources_binary
    exact legVertex_available (finalLegs_available j a)

theorem outside_realizes (j : Fin 48) (hj : outsideRow j)
    (h : Signature ℂ 6) (p : Equiv.Perm (Fin 6)) (K : Native.Binary)
    (hK : Direction (rowForm j) (Matrix.of K))
    (hcard : Signature.contract K (Tensor.reindex p h)=
      complexTensor (coefficientCard (rowForm j) (rowBase j))) :
    Gadget.Realizes (markedResources (rowForm j) h) .disequality
      (Native.binarySignature (complexMatrix (outsideValues j))) := by
  have hcorr : (fun a => complexMatrix (corrections (rowForm j) a))=
      ![Signature.equality,complexMatrix (correction (rowForm j)),
        Signature.equality,complexMatrix (correction (rowForm j))] := by
    funext a
    fin_cases a <;> simp [corrections,MatchingProductBridge.quaternionBasis,MatchingProductBridge.Q0] <;> rfl
  change Gadget.Realizes _ _ (complexTensor (fun x : Fin 2 → Bool => outsideValues j (x 0) (x 1)))
  rw [outside_physical j hj,hcorr,← hcard]
  apply Native.ordered_sparse_realizes_of_mem
  · exact markedResources_ancestor _ _
  · apply markedResources_binary
    exact pairVertex_available hK
  · apply markedResources_binary
    exact legVertex_available (direction_correction _)
  · apply markedResources_binary
    exact legVertex_available (direction_correction _)
  · apply markedResources_binary
    exact pairVertex_available (closureKernel_available j)

/-- The exact native construction uses one initial pair binary plus at most
four further current-group binary vertices. -/
theorem endpoint_network_size (j : Fin 48) (h : Signature ℂ 6)
    (p : Equiv.Perm (Fin 6)) (K : Native.Binary) :
    (Native.orderedDressedNetwork p h K (fun a => complexMatrix (finalLegs j a))).shape.vertices=6 ∧
    (Native.orderedDressedNetwork p h K (fun a => complexMatrix (finalLegs j a))).shape.edges=6 := ⟨rfl,rfl⟩

theorem outside_network_size (j : Fin 48) (h : Signature ℂ 6)
    (p : Equiv.Perm (Fin 6)) (K : Native.Binary) :
    (Native.orderedSparseNetwork p h K (complexMatrix (correction (rowForm j)))
      (complexMatrix (correction (rowForm j))) (complexMatrix (closureKernel j))).shape.vertices=5 ∧
    (Native.orderedSparseNetwork p h K (complexMatrix (correction (rowForm j)))
      (complexMatrix (correction (rowForm j))) (complexMatrix (closureKernel j))).shape.edges=6 := ⟨rfl,rfl⟩

end
end Holant.Certificates.OctahedralSeparator
