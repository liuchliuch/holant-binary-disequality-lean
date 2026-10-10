import Holant.Proofs.Hardness.GeneralEOARSNonclosedSplit
import Holant.Proofs.Hardness.GeneralEOARSNonclosedTransport
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionControlledSource

/-! An original ARS row with nonclosed support supplies either an actual
original-family counting source or an actual original-labelled DEQ4 network.
The selected port comes from the proved finite covariance and support lemmas. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedExtraction
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
namespace P
export GeneralEOARSNonclosedPrefix (complex inclusion)
end P
namespace M
export GeneralEOARSNonclosedMating
  (output network denote central permuted permuted_denote permutedLabels permuted_exact permuted_native)
end M
namespace T
export GeneralEOARSNonclosedTransport (reorder central ars correlation free_pair prefix_permutation)
end T
namespace S
export GeneralEOARSNonclosedSupport (nonclosed_port)
end S
namespace C
export GeneralEOARSNonclosedMass (signature_negative_pair correlation mass)
end C
namespace D
export GeneralEODEQProducerNormalize (Produced produce_reduced)
end D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
variable {s n : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))

theorem extract (label : Fin s) (f : Signature AlgebraicComplex n)
    (slot : (⟨a label.val,G label⟩ : AnySignature AlgebraicComplex)=⟨n,f⟩)
    (he : Signature.CentralSupport f)
    (hf : GeneralEOARSBoundary.ARSUpToScale (P.complex f))
    (nonclosed : ¬GeneralEONegativeClosedSupport.Closed f) :
    GeneralEOPhaseExtractionControlledSource.ControlledCountingHard G ∨ Nonempty (D.Produced G) := by
  classical
  have hn : f≠0 := by
    intro h
    apply nonclosed
    intro x y z hx
    exact False.elim (hx (congrFun h x))
  have hce : Signature.CentralSupport (P.complex f) := by
    intro x hx
    simp [P.complex,he x hx]
  have hcn : P.complex f≠0 := by
    intro h
    apply hn
    funext x
    exact (GeneralEOARSNonclosedPrefix.complex_zero f x).mp (congrFun h x)
  obtain ⟨i,hno⟩ := S.nonclosed_port f nonclosed
  obtain ⟨j,hji,hnegative⟩ := C.signature_negative_pair (P.complex f) hce hcn i
  have htwo : 2≤n := by
    by_contra h
    apply hji
    apply Fin.ext
    omega
  obtain ⟨m,hm⟩ := Nat.exists_eq_add_of_le htwo
  have hn' : n=m+2 := by omega
  clear hm
  subst n
  obtain ⟨e,hei,hej⟩ := T.prefix_permutation i j hji.symm
  have hE : Signature.CentralSupport (T.reorder f e) := T.central f he e
  have hA : GeneralEOARSBoundary.ARSUpToScale (P.complex (T.reorder f e)) := T.ars (P.complex f) hf e
  have hN : C.correlation (C.mass (P.complex (T.reorder f e))) 0 1<0 := by
    change C.correlation (C.mass (T.reorder (P.complex f) e)) 0 1<0
    rw [T.correlation,hei,hej]
    exact hnegative
  let Q := M.permuted f e
  let L := M.permutedLabels G label f slot e
  have hQ : Q.denote=M.output (T.reorder f e) := M.permuted_denote f e
  have labels : LabelledNetwork.Exact G Q L := M.permuted_exact G label f slot e
  have native : ∀k,Q.edge k=Signature.disequality := M.permuted_native f e
  have central : Signature.CentralSupport Q.denote := by
    rw [hQ]
    simpa only [M.denote] using M.central (T.reorder f e) hE
  rcases GeneralEOARSNonclosedSplit.split (T.reorder f e) hE hA hN with hard|pair|free
  · left
    apply GeneralEOPhaseExtractionControlledSource.controlled_hard G Q L labels native central
    rwa [hQ]
  · right
    obtain ⟨pair⟩ := pair
    let reduced : GeneralEODEQProducerReduction.Reduced G :=
      ⟨Q,L,labels,native,central,by simpa only [hQ] using pair⟩
    exact D.produce_reduced G reduced
  · have h := T.free_pair f e 0 1 free
    rw [hei,hej] at h
    exact False.elim (hno j h)

theorem selected (label : Fin s)
    (he : Signature.CentralSupport (G label))
    (hf : GeneralEOARSBoundary.ARSUpToScale (P.complex (G label)))
    (nonclosed : ¬GeneralEONegativeClosedSupport.Closed (G label)) :
    GeneralEOPhaseExtractionControlledSource.ControlledCountingHard G ∨ Nonempty (D.Produced G) :=
  extract G label (G label) rfl he hf nonclosed

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedExtraction
