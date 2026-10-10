import Holant.Dihedral.SectorRuling.SampleSelection

/-! Every nonzero source sample is put into the one matching derived from
support rigidity, retaining its actual matrix factors and original scalar. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant Holant.Marked Holant.Certificates Holant.Dihedral.CompatibleClosure
open Holant.Dihedral.EndpointParallelogram Holant.Dihedral.CompatibleCoefficientLine
set_option backward.isDefEq.respectTransparency false

theorem common_representation {m r : ℕ} (hm : 3 ≤ m) (U V : Signature Scalar (2*(r+1)))
    (hs : ∀ t : Scalar,Roots m t → tensorPencil U V t=0 ∨ MatchingSample m (r+1) (tensorPencil U V t))
    (a : Scalar) (ha : Roots m a) (hna : tensorPencil U V a ≠ 0)
    (p : (Fin (r+1) × Bool) ≃ Fin (2*(r+1))) (A : Fin (r+1) → Mat) (κ : Scalar)
    (hA : ∀ e,A e ∈ groupM m) (hκ : κ ≠ 0)
    (hq : tensorPencil U V a=MatchingContractionClosure.productValue p A κ)
    (t : Scalar) (ht : Roots m t) (hnt : tensorPencil U V t ≠ 0) :
    ∃ B : Fin (r+1) → Mat, ∃ c : Scalar,(∀ e,B e ∈ groupM m) ∧ c ≠ 0 ∧
      tensorPencil U V t=MatchingContractionClosure.productValue p B c := by
  obtain ⟨p',B,c,hB,hc,hq'⟩ := (hs t ht).resolve_left hnt
  have hsupport := source_common_support hm U V hs a t ha ht hna hnt
  rw [hq,hq'] at hsupport
  have hmatching := matching_of_support_eq p p' A B κ c
    (fun e => groupM_isMonomial (by omega) (hA e)) (fun e => groupM_isMonomial (by omega) (hB e)) hκ hc hsupport
  let L := MatchingAlignment.ofMate p p' (fun u => congrArg (fun P : Pairing _ => P.mate u) hmatching)
  refine ⟨L.factors B,c,?_,hc,?_⟩
  · intro e
    unfold MatchingAlignment.factors
    split
    · exact transpose_group_mem (by omega) (hB _)
    · exact hB _
  · exact hq'.trans (L.product_eq B c).symm

end Holant.Dihedral.SectorRuling
