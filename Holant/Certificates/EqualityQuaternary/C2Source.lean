import Holant.Certificates.EqualityQuaternary.C2MixedNormalize

/-! Complete C2 row of A.7/A.8. Source retained-state membership q∈Λ and
literal I∈Λ is retained, and the supplied actual representative deck includes
all zeros, all six pairs, and both residual orders. Every constructed graph
has only original-q and literal-I vertices and all edges native X.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2
open Holant Holant.Marked Holant.Tractable
open Holant.EightVertex.ProductAnchor (EndpointEven)
set_option backward.isDefEq.respectTransparency false

theorem flip_counted_allowed (q : Signature Scalar 4) (mask : Fin 4 → Bool) :
    Counted.Allowed q (Flip.network q mask) := by
  refine ⟨?_,Flip.native q mask⟩
  intro v
  by_cases hv : v=Flip.ancestor q mask
  · exact Or.inl (hv ▸ (Flip.labels_exact q mask).1)
  · exact Or.inr ((Flip.labels_exact q mask).2 v hv)

theorem flip_counted_copies (q : Signature Scalar 4) (mask : Fin 4 → Bool) :
    Counted.copies (Flip.network q mask)=1 := by
  classical
  simpa [Counted.copies] using Flip.quaternary_count q mask

/-- Contracted-port reversal does not alter either fixed actual C2 matrix. -/
theorem representative_transpose {F : SignatureFamily Scalar} (reps : Representatives F) (p : Bool) :
    Kernel.transpose (reps.matrix p)=reps.matrix p := by
  rw [reps.normal_form]
  funext a b
  cases p <;> cases a <;> cases b <;>
    simp [binary,scale,Kernel.transpose,Signature.equality,Signature.disequality]

/-- Mixed-sign clause of A.8(i), with normalization derived from physical
safety and the exact two-original-q network supplied in the conclusion. -/
theorem source_C2_mixed_boundary (F : SignatureFamily Scalar) (reps : Representatives F)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : PhysicalDeck reps q) (hm : ¬OneCopyCase q) :
    ∃ N : Network Scalar 4, Counted.Allowed q N ∧ Counted.copies N=2 ∧
      EndpointEven N.denote ∧ ¬GroupMatching group N.denote ∧ Gadget.Realizes F .disequality N.denote := by
  obtain ⟨b,e,x,y,z,hx,hz,hform⟩ := Mixed.source_mixed_normalization reps q hd hm
  let M := Mixed.normalizedNetwork (Counted.input q) b e
  have hM : M.denote=Mixed.normalized q b e := by
    dsimp [M]
    rw [Mixed.normalized_denote,Counted.input_denote]
  have hallowed := Mixed.normalized_allowed (Counted.input_allowed q) b e
  obtain ⟨p,he,hn⟩ := Mixed.normalized_mixed_exit (Mixed.normalized q b e) x y z
    (Mixed.normalized_prime hp b e) hx hz hform
  refine ⟨Mixed.network M p,Mixed.allowed hallowed p,?_,?_,?_,?_⟩
  · rw [Mixed.copies,Mixed.normalized_copies,Counted.input_copies]
  · rwa [Mixed.denote,hM]
  · rwa [Mixed.denote,hM]
  · exact (Mixed.allowed hallowed p).realizes F hq hI

/-- Complete physical C2 certificate, covering both one-copy and mixed-sign
cases without a classification or realization oracle. -/
theorem source_C2_boundary (F : SignatureFamily Scalar) (reps : Representatives F)
    (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : PhysicalDeck reps q) :
    ∃ N : Network Scalar 4, Counted.Allowed q N ∧ Counted.copies N≤2 ∧
      EndpointEven N.denote ∧ ¬GroupMatching group N.denote ∧ Gadget.Realizes F .disequality N.denote := by
  classical
  by_cases hm : OneCopyCase q
  · obtain ⟨mask,he⟩ := source_C2_one_copy_endpoint reps q hp.1 hd hm
    have hn : ¬GroupMatching group (Flip.value q mask) := prime_not_matching (flip_prime hp mask)
    have ha := flip_counted_allowed q mask
    refine ⟨Flip.network q mask,ha,?_,?_,?_,ha.realizes F hq hI⟩
    · rw [flip_counted_copies]
      decide
    · rwa [Flip.denote]
    · rwa [Flip.denote]
  · obtain ⟨N,ha,hc,he,hn,hr⟩ := source_C2_mixed_boundary F reps q hp hq hI hd hm
    exact ⟨N,ha,by omega,he,hn,hr⟩

end Holant.Certificates.EqualityQuaternary.C2
