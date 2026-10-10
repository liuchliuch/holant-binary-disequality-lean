import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRulingStep
import Holant.Certificates.MatchingContractionClosure.PortSurgery
import Holant.Certificates.MatchingContractionClosure.SinglePair

/-! The mate formula used by disagreement reduction is proved equal to the
shared surgery on literal original ports. Edge re-enumeration and orientation
changes preserve the physical mate relation. -/
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section
namespace MatchingSurgery
open Holant.Certificates.MatchingContractionClosure
variable {P J : Type*} [DecidableEq P] [DecidableEq J]

 def portsMate (ports : (J × Bool) ≃ P) (w : P) : P :=
  ports ((ports.symm w).1,!(ports.symm w).2)

 @[simp] theorem portsMate_port (ports : (J × Bool) ≃ P) (e : J) (b : Bool) :
     portsMate ports (ports (e,b)) = ports (e,!b) := by
   simp only [portsMate,Equiv.symm_apply_apply]

 def spliceMate (ports : (J × Bool) ≃ P) (u v w : P) : P :=
   if portsMate ports w = u then portsMate ports v
   else if portsMate ports w = v then portsMate ports u else portsMate ports w

 theorem portsMate_splice (ports : (J × Bool) ≃ P) (e f : J)
     (w : Remaining (ports (e,true)) (ports (f,false))) :
     (portsMate (splicePorts ports e f) w).val =
       spliceMate ports (ports (e,true)) (ports (f,false)) w.val := by
   obtain ⟨⟨d,b⟩,rfl⟩ := (splicePorts ports e f).surjective w
   rw [portsMate_port,splicePorts_val,splicePorts_val]
   by_cases hd : d.val = e
   · cases b <;> simp only [hd,ite_true,Bool.not_false,Bool.not_true,spliceMate,
       portsMate_port,Equiv.apply_eq_iff_eq,Prod.mk.injEq,Bool.false_eq_true,and_false,
       ite_false]
   · cases b <;> simp [hd,spliceMate,portsMate_port,Equiv.apply_eq_iff_eq,d.property]

 theorem portsMate_flip (ports : (J × Bool) ≃ P) (mask : J → Bool) (w : P) :
     portsMate ((flipSlots mask).trans ports) w = portsMate ports w := by
   obtain ⟨⟨e,b⟩,rfl⟩ := ((flipSlots mask).trans ports).surjective w
   rw [portsMate_port]
   change ports (e,(!b) ^^ mask e) = portsMate ports (ports (e,b ^^ mask e))
   rw [portsMate_port]
   cases b <;> cases hm : mask e <;> rfl

 theorem portsMate_matching {r : ℕ} (M : Matching P r) (w : P) : portsMate M.ports w = M.mate w := by
   obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective w
   rw [portsMate_port,M.mate_port]

 theorem spliceMate_matching {r : ℕ} (M : Matching P r) (u v w : P) :
     spliceMate M.ports u v w = M.spliceMateValue u v w := by
   simp only [spliceMate,Matching.spliceMateValue,portsMate_matching]

 variable [Fintype J]

 /-- The shared finite-edge port bijection as the existing matching structure. -/
 def matching (ports : (J × Bool) ≃ P) : Matching P (Fintype.card J) :=
   ⟨(Equiv.prodCongr (Fintype.equivFin J).symm (Equiv.refl Bool)).trans ports⟩

 theorem matching_mate (ports : (J × Bool) ≃ P) (w : P) :
     (matching ports).mate w = portsMate ports w := by
   obtain ⟨⟨e,b⟩,rfl⟩ := ports.surjective w
   have hp : (matching ports).ports (Fintype.equivFin J e,b) = ports (e,b) := by
     simp [matching]
   rw [←hp,(matching ports).mate_port]
   simp [matching,portsMate_port]

end MatchingSurgery
end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
