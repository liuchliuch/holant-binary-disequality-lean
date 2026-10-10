import Holant.ReedMuller.WeightTwoIntegration.Logical
import Holant.ReedMuller.WeightTwoIntegration.WeightedDeck

/-! Every nonzero actual same-pair card retains the complete matching on the
other original edges. Its coefficients may change; its full support is proved. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
variable {K : Type*} [Field K] {n : ℕ} {f : Signature K n}
set_option backward.isDefEq.respectTransparency false

 theorem WeightedProduct.support_spec {ι : Type*} (P : WeightedProduct K ι) (x : ι → Bool) :
    P.value x≠0 ↔ (Pairing.ofPorts P.ports).Support x := by
  rw [P.value_nonzero_iff,Pairing.ofPorts_support]

 theorem OriginalPairing.same_pair_boundary_nonzero (C : OriginalPairing f)
    (htwo : (2:K)≠0) (hd : EqualityDeck f) (hn : 6≤n) (i : Fin C.count) (minus : Bool)
    (P : WeightedProduct K (Remaining (C.ports (i,false)) (C.ports (i,true))))
    (hP : card f (C.ports (i,false)) (C.ports (i,true)) minus=P.value)
    (x : Fin n → Bool) (hx : C.matching.Support x) : P.value (fun p=>x p.val)≠0 := by
  let u := C.ports (i,false)
  let v := C.ports (i,true)
  have huv : u≠v := (C.port_edge i).1
  have hmu : C.matching.mate u=v := originalPorts_mate C.matching i false
  have hmv : C.matching.mate v=u := originalPorts_mate C.matching i true
  have hwhole : card f u v minus≠0 := by
    rw [hP]
    intro hz
    have hnon := (P.value_nonzero_iff (fun _=>false)).mpr (fun _=>rfl)
    exact hnon (congrFun hz _)
  apply (P.support_spec _).mpr
  intro p
  have hqu : C.matching.mate p.val≠u := by
    intro hh
    have he := (C.matching.mate_eq_iff p.val u).mp hh
    rw [hmu] at he
    exact p.property.2 he.symm
  have hqv : C.matching.mate p.val≠v := by
    intro hh
    have he := (C.matching.mate_eq_iff p.val v).mp hh
    rw [hmv] at he
    exact p.property.1 he.symm
  let q : Remaining u v := ⟨C.matching.mate p.val,hqu,hqv⟩
  have hpq : p≠q := by
    intro he
    exact C.matching.ne_self p.val (congrArg Subtype.val he).symm
  have hW : (weightGraph f).Adj p.val q.val := (C.edge_iff _ _).mp rfl
  have he := hd.card_pair_of_weight_edge htwo (by simpa using hn) u v huv p q hW minus hwhole
  rw [hP] at he
  have hm := ((Pairing.ofPorts P.ports).support_pair_iff p q hpq).mp ((P.support_spec _).mp he)
  rw [hm]
  exact hx p.val

end Holant.ReedMuller.WeightTwoIntegration
