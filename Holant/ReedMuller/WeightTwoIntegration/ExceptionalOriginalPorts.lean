import Holant.ReedMuller.WeightTwoIntegration.ExceptionalSource

/-! Transport the fixed exceptional incidence back to the original six ports.
Only the two source vertices are rewired. Their labels remain the original f. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open scoped BigOperators
open CoefficientAtlas ExceptionalTopology
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

def originalBase (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6)
    (C : Fin 4 → Kernel ℂ) : FiniteNetwork ℂ Bool (Fin 4) 4 where
  arity := fun _ => 6
  ports := (Equiv.sigmaCongrRight (fun _ : Bool => p)).trans ports
  vertex := fun _ => f
  edge := C

/-- Port i of each original f is routed to canonical port p(i), literally. -/
theorem originalBase_port (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6)
    (C : Fin 4 → Kernel ℂ) (b : Bool) (i : Fin 6) :
    (originalBase p f C).ports ⟨b,i⟩ = ports ⟨b,p i⟩ := rfl

theorem originalBase_denote (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6)
    (C : Fin 4 → Kernel ℂ) :
    (originalBase p f C).denote = (network (Tensor.reindex p f) C).denote := rfl

def originalPhysicalNetwork {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) :
    FiniteNetwork ℂ (Bool ⊕ Fin 4) (Fin 4 × Bool) 4 :=
  ExceptionalLinks.subdivide (originalBase p f (fun _ => Signature.disequality)) (linkKernels d B)

theorem originalPhysicalNetwork_denote {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) :
    (originalPhysicalNetwork d B p f).denote =
      (physicalNetwork d B (Tensor.reindex p f)).denote := by
  rw [originalPhysicalNetwork,physicalNetwork,ExceptionalLinks.denote_subdivide,
    ExceptionalLinks.denote_subdivide]
  rfl

theorem originalPhysicalNetwork_uses {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6)
    (hf : (⟨6,f⟩ : AnySignature ℂ) ∈ family) :
    ∀ v, (⟨(originalPhysicalNetwork d B p f).arity v,
      (originalPhysicalNetwork d B p f).vertex v⟩ : AnySignature ℂ) ∈ family := by
  rintro (b|e)
  · exact hf
  · exact B.available (linkSigns d e)

theorem originalPhysicalNetwork_two_copies {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) :
    TwoSixPortCopies (originalPhysicalNetwork d B p f) f :=
  physicalNetwork_two_copies d B f

theorem originalDressedNetwork_two_copies {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (p : Equiv.Perm (Fin 6)) (f : Signature ℂ 6) (c : ℂ) :
    TwoSixPortCopies (ExceptionalDressing.attachI (originalPhysicalNetwork d B p f) c) f :=
  dressedNetwork_two_copies d B f c

/-- Full original-port version, requiring only original f and the fixed actual
binary representatives in the family. No reindex closure premise is needed. -/
theorem exceptional_original_two_copy_even4 {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (f : Signature ℂ 6)
    (hfmem : (⟨6,f⟩ : AnySignature ℂ) ∈ family)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tensor.reindex p f =
      fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    ∃ N : Network ℂ 4, ∃ s : ℂ,
      s ≠ 0 ∧ N.denote = (fun x => s * even4 x) ∧
      N.shape.vertices ≤ 7 ∧ N.shape.edges ≤ 9 ∧
      Fintype.card {v : Fin N.shape.vertices // N.shape.arity v = 6} = 2 ∧
      (∀ v, N.shape.arity v = 6 → HEq (N.vertex v) f) ∧
      (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family) ∧
      (∀ e, N.edge e = Signature.disequality) := by
  have hs : physicalScale d B c * (2 * d.coefficient) ≠ 0 :=
    mul_ne_zero (physicalScale_ne_zero d B c hc)
      (mul_ne_zero (by norm_num) d.coefficient_ne_zero)
  have hu := originalPhysicalNetwork_uses d B p f hfmem
  have hd := (originalPhysicalNetwork_denote d B p f).trans
    (physicalNetwork_denote d B (Tensor.reindex p f) c hf)
  rcases d.sigma_sign with hσ | hσ
  · refine ⟨(originalPhysicalNetwork d B p f).toNetwork,
      physicalScale d B c * (2 * d.coefficient),hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hu,?_⟩
    · rw [FiniteNetwork.denote_toNetwork,hd,exceptional_reconstruction_even d hσ]
      funext x
      ring
    · simp [originalPhysicalNetwork,ExceptionalLinks.vertex_count]
    · simp [originalPhysicalNetwork,ExceptionalLinks.edge_count]
    · exact (two_copies_toNetwork _ f (originalPhysicalNetwork_two_copies d B p f)).1
    · exact (two_copies_toNetwork _ f (originalPhysicalNetwork_two_copies d B p f)).2
    · intro e
      rfl
  · let N := ExceptionalDressing.attachI (originalPhysicalNetwork d B p f) (B.scale false)
    have hN : ∀ v, (⟨N.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ family := by
      rintro (v|u)
      · exact hu v
      · exact B.available false
    refine ⟨N.toNetwork,B.scale false * (physicalScale d B c * (2 * d.coefficient)),
      mul_ne_zero (B.nonzero false) hs,?_,?_,?_,?_,?_,uses_toNetwork _ _ hN,?_⟩
    · rw [FiniteNetwork.denote_toNetwork]
      change (ExceptionalDressing.attachI (originalPhysicalNetwork d B p f) (B.scale false)).denote = _
      rw [ExceptionalDressing.denote_attachI,hd,exceptional_reconstruction_odd d hσ]
      funext x
      dsimp only
      rw [flipFirst_twice]
      ring
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.vertices ≤ 7
      rw [ExceptionalDressing.vertex_count]
      norm_num
    · change (ExceptionalDressing.attachI _ _).toNetwork.shape.edges ≤ 9
      rw [ExceptionalDressing.edge_count]
      norm_num
    · exact (two_copies_toNetwork _ f (originalDressedNetwork_two_copies d B p f (B.scale false))).1
    · exact (two_copies_toNetwork _ f (originalDressedNetwork_two_copies d B p f (B.scale false))).2
    · intro e
      change N.edge _ = _
      generalize (Fintype.equivFin ((Fin 4 × Bool) ⊕ Unit)).symm e = w
      cases w <;> rfl

theorem exceptional_original_realizes_even4 {family : SignatureFamily ℂ} (d : ExceptionalData)
    (B : ExceptionalBinaries family) (f : Signature ℂ 6)
    (hfmem : (⟨6,f⟩ : AnySignature ℂ) ∈ family)
    (p : Equiv.Perm (Fin 6)) (c : ℂ) (hc : c ≠ 0)
    (hf : Tensor.reindex p f =
      fun x => c * Signature.coordinateAction (fun _ => walshKernel) (paired d.h) x) :
    Gadget.RealizesUpTo family .disequality even4 := by
  obtain ⟨N,s,hs,hden,_,_,_,_,hv,he⟩ :=
    exceptional_original_two_copy_even4 d B f hfmem p c hc hf
  refine ⟨s,hs,?_⟩
  rw [← hden]
  exact Gadget.realizes_network N family .disequality hv he

end Holant.ReedMuller.WeightTwoIntegration
