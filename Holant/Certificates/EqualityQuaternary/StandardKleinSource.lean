import Holant.Certificates.EqualityQuaternary.KleinClassification
import Holant.Certificates.EqualityQuaternary.StandardKleinPlanes
import Holant.Certificates.EqualityQuaternary.C2Source

/-! Standard Pauli Klein row of A.7/A.8: the four maximal parity/complement
planes are consequences of the complete physical deck and exact cover.
One literal equality dressing produces the prime nonmatching exit.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.EightVertex.ProductAnchor (EndpointEven)
open Finite
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- All four planes are explicitly classified from the actual six-pair deck. -/
theorem source_standard_planes {F : SignatureFamily Scalar}
    (reps : Representatives F .standard) (q : Signature Scalar 4) (h : PhysicalDeck reps q) :
    ∃ j : Fin 4, (∀ w,parity w≠standardParity j → q w=0) ∧
      ∀ w,q (complement w)=standardSign j*q w := by
  obtain ⟨p,c,j,hq,hplane⟩ := source_klein_plane reps q h
  refine ⟨j,?_,?_⟩
  · intro w hw
    rw [hq,plane_expansion .standard p c j hplane]
    apply Finset.sum_eq_zero
    intro r _
    rw [standard_support j r w hw,mul_zero]
  · intro w
    rw [hq,plane_expansion .standard p c j hplane,plane_expansion .standard p c j hplane,
      Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    rw [standard_complement]
    ring

def group (kind : Kind) : Set Mat := {B | ∃ k c,c≠0 ∧ B=scale c (E kind k)}

theorem source_standard_endpoint {F : SignatureFamily Scalar}
    (reps : Representatives F .standard) (q : Signature Scalar 4) (hq : q≠0) (h : PhysicalDeck reps q) :
    ∃ mask : Word,EndpointEven (Flip.value q mask) := by
  obtain ⟨j,hpar,hcomp⟩ := source_standard_planes reps q h
  obtain ⟨mask,hmask⟩ : ∃ mask,q mask≠0 := by
    by_contra hh
    push Not at hh
    exact hq (funext hh)
  have hpm : parity mask=standardParity j := by
    by_contra hh
    exact hmask (hpar mask hh)
  have hs : standardSign j≠0 := by unfold standardSign; split_ifs <;> norm_num
  refine ⟨mask,?_,?_,?_⟩
  · simpa [Flip.value,xorWord] using hmask
  · have hc : q (complement mask)≠0 := by rw [hcomp]; exact mul_ne_zero hs hmask
    simpa [Flip.value,xorWord,complement] using hc
  · intro w hw
    change q (xorWord w mask)=0
    apply hpar
    rw [parity_xorWord,(parity_weight w).mpr hw,hpm]
    cases standardParity j <;> decide

/-- Complete standard Klein boundary certificate, with exactly one original
q vertex and literal-I auxiliaries in an exact native-X graph. -/
theorem source_standard_boundary (F : SignatureFamily Scalar)
    (reps : Representatives F .standard) (q : Signature Scalar 4) (hp : TensorPrime q)
    (hq : (⟨4,q⟩ : AnySignature Scalar)∈F)
    (hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature Scalar)∈F)
    (hd : PhysicalDeck reps q) :
    ∃ N : Network Scalar 4,Counted.Allowed q N ∧ Counted.copies N=1 ∧
      EndpointEven N.denote ∧ TensorPrime N.denote ∧ ¬GroupMatching (group .standard) N.denote ∧
      Gadget.Realizes F .disequality N.denote := by
  obtain ⟨mask,he⟩ := source_standard_endpoint reps q hp.1 hd
  have ha := C2.flip_counted_allowed q mask
  have hp' := flip_prime hp mask
  refine ⟨Flip.network q mask,ha,C2.flip_counted_copies q mask,?_,?_,?_,ha.realizes F hq hI⟩
  · rwa [Flip.denote]
  · rwa [Flip.denote]
  · rw [Flip.denote]
    exact prime_not_matching hp'

end Holant.Certificates.EqualityQuaternary.Klein
