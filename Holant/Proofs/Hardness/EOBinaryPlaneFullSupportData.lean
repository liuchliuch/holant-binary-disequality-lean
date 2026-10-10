import Holant.Proofs.Hardness.ComplexPlaneThreeSupportData
import Holant.Proofs.Hardness.EOBinaryPlanePositive
import Holant.Proofs.Hardness.OriginalPortAccess

/-! Original-only conditions for the three full-support opposite-pair EO
planes. The plane order and binary compression are selected internally, and
literal EOTract failure implies the two coefficient obstructions required by
the finite positive-table producer. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportData
open Holant Holant.Tractable
namespace D
export ComplexPlaneThreeSupportData
  (support mem_support support_card_lift support_card_reindex Plane planeIndex plane_zero binary)
end D
namespace B
export EOBinaryPlaneCore (normalized compress lift normalized_lift normalized_eo normalized_corners)
end B
namespace P
export EOBinaryPlanePositive (exceptional exceptional_affine)
end P
namespace G
export EOBinaryPlaneGram (determinant)
end G
namespace A
export OriginalPortAccess (normalized_algebraic controlled)
end A
set_option backward.isDefEq.respectTransparency false

variable (M : Signature ℂ 4)
def ExactlyFour : Prop := (D.support M).card=4
variable (hp : D.Plane M) (he : DenseEOUnitLocal.EOSupport M) (hf : ExactlyFour M)

abbrev signature := B.normalized M (D.planeIndex M hp)
abbrev binary := D.binary M hp

include he in
theorem signature_lift : signature M hp=B.lift (binary M hp) :=
  (B.normalized_lift M he (D.planeIndex M hp) (D.plane_zero M hp).1 (D.plane_zero M hp).2).symm

include he hf in
theorem binary_full : ∀z,binary M hp z≠0 := by
  classical
  have hc : (D.support (binary M hp)).card=4 := by
    rw [←D.support_card_lift,←signature_lift M hp he]
    exact (D.support_card_reindex M _).trans hf
  have hu : D.support (binary M hp)=Finset.univ := Finset.eq_univ_of_card _ (by simpa using hc)
  intro z
  apply (D.mem_support _ _).mp
  rw [hu]
  exact Finset.mem_univ _

variable (halg : ∀x,IsAlgebraic ℚ (M x))

def algebraic : Signature AlgebraicComplex 4 := fun x=>⟨M x,(halg x).isIntegral⟩
def algebraicBinary : Signature AlgebraicComplex 2 :=
  B.compress (B.normalized (algebraic M halg) (D.planeIndex M hp))

abbrev signature_algebraic := A.normalized_algebraic M halg (FiveSupportEOOrdering.orderAt (D.planeIndex M hp))
abbrev portSource := A.controlled M halg (FiveSupportEOOrdering.orderAt (D.planeIndex M hp))

theorem algebraic_binary_value (z : Fin 2→Bool) : (algebraicBinary M hp halg z : ℂ)=binary M hp z := rfl

include he hf in
theorem algebraic_binary_full : EOBinaryPlaneClassification.Full (algebraicBinary M hp halg) := by
  intro z hz
  exact binary_full M hp he hf z (congrArg Subtype.val hz)

include he in
theorem algebraic_eo : DenseEOUnitLocal.EOSupport (algebraic M halg) := by
  intro x hx
  apply Subtype.ext
  exact he x hx

theorem algebraic_plane_zero :
    FiveSupportEOOrdering.middleCoeff (algebraic M halg) (D.planeIndex M hp)=0 ∧
      FiveSupportEOOrdering.middleCoeff (algebraic M halg) (5-D.planeIndex M hp)=0 := by
  constructor
  · apply Subtype.ext
    exact (D.plane_zero M hp).1
  · apply Subtype.ext
    exact (D.plane_zero M hp).2

variable (hn : ¬EOTract {⟨4,algebraic M halg⟩})

include he hn in
theorem binary_nontract : ¬Affine (algebraicBinary M hp halg) ∧ ¬Product (algebraicBinary M hp halg) := by
  have h := EOBinaryPlaneTract.plane_tract_iff (algebraic M halg) (algebraic_eo M he halg)
    (D.planeIndex M hp) (algebraic_plane_zero M hp halg).1 (algebraic_plane_zero M hp halg).2
  exact ⟨fun ha=>hn (h.mpr (Or.inl ha)),fun hp=>hn (h.mpr (Or.inr hp))⟩

include he hf hn in
theorem coefficient_obstructions :
    G.determinant (binary M hp ![false,false]) (binary M hp ![false,true])
      (binary M hp ![true,false]) (binary M hp ![true,true])≠0 ∧
    ¬P.exceptional (binary M hp ![false,false]) (binary M hp ![false,true])
      (binary M hp ![true,false]) (binary M hp ![true,true]) := by
  have hfull := algebraic_binary_full M hp he hf halg
  obtain ⟨hna,hnp⟩ := binary_nontract M hp he halg hn
  constructor
  · intro hz
    apply hnp
    apply (EOBinaryPlaneClassification.full_product_iff _ hfull).mpr
    exact Subtype.ext (sub_eq_zero.mp hz)
  · intro hx
    apply hna
    exact P.exceptional_affine (algebraicBinary M hp halg) hfull hx

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportData
