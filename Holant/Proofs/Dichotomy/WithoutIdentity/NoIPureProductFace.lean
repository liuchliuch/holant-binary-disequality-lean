import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeNonproductBundleSupport

/-! Signed full binary extraction from a Product fourth power.  The two
logical coordinates retain all original signed incidences. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductFace
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace S
export OrdinaryNegativeNonproductBundleSupport
  (flip shifted signedWord product_shifted_iff product_flip product_signed_substitute)
export GeneralEOPairedFamilyExtractionSupport (origin XorClosed MeetClosed product_meetClosed)
end S
namespace C
export GeneralEOPairedFamilyExtractionComponentsFull
  (substitution reduced expand_substitute exists_nonproduct_face)
end C
namespace I
export GeneralEOPairedFamilyExtractionInteraction (compose facePorts substitute_compose face_substitute)
end I
namespace B
export EOBinaryPlaneClassification (Full)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option maxHeartbeats 900000
set_option Elab.async false
variable {n : ℕ}

theorem fourth_closed (f : Signature AlgebraicComplex n) (h0 : f S.origin≠0)
    (hp : Product (fun x=>f x^4)) : S.XorClosed f ∧ S.MeetClosed f := by
  constructor
  · intro u v hu hv
    have hh:=product_support_xor3 hp u v S.origin
      (pow_ne_zero 4 hu) (pow_ne_zero 4 hv) (pow_ne_zero 4 h0)
    have hn : f (xor3 u v S.origin)≠0:=
      (pow_ne_zero_iff (by decide : 4≠0)).mp hh
    convert hn using 1
    congr 1
    funext i
    simp [xor3,S.origin,GeneralEOPairedFamilyExtractionSupport.xor]
  · intro u v hu hv
    exact (pow_ne_zero_iff (by decide : 4≠0)).mp
      (S.product_meetClosed _ (pow_ne_zero 4 h0) hp u v
        (pow_ne_zero 4 hu) (pow_ne_zero 4 hv))

structure Face (f : Signature AlgebraicComplex n) where
  base : Fin n→Bool
  ports : Fin n→Bool⊕Fin 2
  full : B.Full (fun z=>f (S.signedWord base ports z))
  nonproduct : ¬Product (fun z=>f (S.signedWord base ports z))
  fourth : Product (fun z=>f (S.signedWord base ports z)^4)

namespace Face
variable {f : Signature AlgebraicComplex n}
def binary (D : Face f) : Signature AlgebraicComplex 2:=
  fun z=>f (S.signedWord D.base D.ports z)

end Face

theorem exists_face (f : Signature AlgebraicComplex n) (hn : ¬Product f)
    (hf : Product (fun x=>f x^4)) : Nonempty (Face f) := by
  classical
  have nonzero : f≠0:=fun h=>hn (Or.inl h)
  obtain ⟨s,hs⟩:=Function.ne_iff.mp nonzero
  change f s≠0 at hs
  let g:=S.shifted f s
  have h0 : g S.origin≠0:=by
    simpa only [g,S.shifted,OrdinaryNegativeNonproductBundleSupport.flip_origin] using hs
  have hg : ¬Product g:=fun h=>hn ((S.product_shifted_iff s f).mp h)
  have hfourth : Product (fun x=>g x^4):=S.product_flip s hf
  obtain ⟨hx,hm⟩:=fourth_closed g h0 hfourth
  obtain ⟨i,j,hij,x,hfull,hprod⟩:=C.exists_nonproduct_face g h0 hx hm hg
  let p:=I.compose (C.substitution g) (I.facePorts i j x)
  have equation : (fun z=>f (S.signedWord s p z))=
      GeneralEOPairedFamilyExtractionFullSupport.face (C.reduced g) i j x := by
    funext z
    change g (GeneralEOPairedFamilyExtractionTensor.substitute p z)=_
    rw [show p=I.compose (C.substitution g) (I.facePorts i j x) from rfl,
      I.substitute_compose,←C.expand_substitute]
    exact I.face_substitute (C.reduced g) i j x z
  refine ⟨⟨s,p,?_,?_,S.product_signed_substitute s p hf⟩⟩
  · rwa [equation]
  · rwa [equation]

def extract (f : Signature AlgebraicComplex n) (hn : ¬Product f)
    (hf : Product (fun x=>f x^4)) : Face f:=Classical.choice (exists_face f hn hf)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPureProductFace
end
