import Holant.Pauli.ExoticKlein.RulingSurgery

namespace Holant.Pauli.ExoticKlein
noncomputable section
namespace MatchingSurgery
open Holant.Certificates.MatchingContractionClosure
variable {P J : Type*} [DecidableEq P] [DecidableEq J]

 def castSplicePorts (ports : (J × Bool) ≃ P) (e f : J) (u v : P)
     (hu : ports (e,true) = u) (hv : ports (f,false) = v) :
     (OtherEdges f × Bool) ≃ Remaining u v :=
   (splicePorts ports e f).trans (Equiv.subtypeEquivRight (fun x => by rw [hu,hv]))

 theorem portsMate_castSplice (ports : (J × Bool) ≃ P) (e f : J) (u v : P)
     (hu : ports (e,true) = u) (hv : ports (f,false) = v) (w : Remaining u v) :
     (portsMate (castSplicePorts ports e f u v hu hv) w).val = spliceMate ports u v w.val := by
   subst u
   subst v
   exact portsMate_splice ports e f w

 variable {r : ℕ}

 def edgeIndex (M : Matching P r) (u : P) : Fin r := (M.ports.symm u).1

 theorem edgeIndex_ne (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v) :
     edgeIndex M u ≠ edgeIndex M v := by
   obtain ⟨⟨e,b⟩,rfl⟩ := M.ports.surjective u
   obtain ⟨⟨f,c⟩,rfl⟩ := M.ports.surjective v
   intro he
   change (M.ports.symm (M.ports (e,b))).1 = (M.ports.symm (M.ports (f,c))).1 at he
   simp only [Equiv.symm_apply_apply] at he
   subst f
   cases b <;> cases c
   · exact huv rfl
   · exact hc (M.mate_port e false)
   · exact hc (M.mate_port e true)
   · exact huv rfl

 def crossOrientedPorts (M : Matching P r) (u v : P) : (Fin r × Bool) ≃ P :=
   (flipSlots (crossMask M.ports u v)).trans M.ports

 theorem crossOriented_selected (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v) :
     crossOrientedPorts M u v (edgeIndex M u,true) = u ∧
       crossOrientedPorts M u v (edgeIndex M v,false) = v :=
   cross_selected_ports M.ports u v (edgeIndex_ne M u v huv hc)

 def crossResidualPorts (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v) :
     (OtherEdges (edgeIndex M v) × Bool) ≃ Remaining u v :=
   castSplicePorts (crossOrientedPorts M u v) (edgeIndex M u) (edgeIndex M v) u v
     (crossOriented_selected M u v huv hc).1 (crossOriented_selected M u v huv hc).2

 def crossMatching (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v) :
     Matching (Remaining u v) (Fintype.card (OtherEdges (edgeIndex M v))) :=
   matching (crossResidualPorts M u v huv hc)

 theorem crossMatching_mate (M : Matching P r) (u v : P) (huv : u ≠ v) (hc : M.mate u ≠ v)
     (w : Remaining u v) : ((crossMatching M u v huv hc).mate w).val = M.spliceMateValue u v w.val := by
   rw [crossMatching,matching_mate]
   unfold crossResidualPorts
   rw [portsMate_castSplice]
   simp only [spliceMate,crossOrientedPorts,portsMate_flip,portsMate_matching,Matching.spliceMateValue]

/-- The combinatorial disagreement lemma produces genuinely different actual
residual perfect matchings on the same original surviving port set. -/
 theorem actual_disagreement_reduction [Fintype P] {s : ℕ} (M : Matching P r) (N : Matching P s)
     (hne : M.mate ≠ N.mate) (hcard : 4 < Fintype.card P) :
     ∃ u v : P, ∃ huv : u ≠ v, ∃ hM : M.mate u ≠ v, ∃ hN : N.mate u ≠ v,
       (crossMatching M u v huv hM).mate ≠ (crossMatching N u v huv hN).mate := by
   obtain ⟨u,v,w,huv,hM,hN,hwu,hwv,hd⟩ := M.distinct_rulings_have_reduction_pair N hne hcard
   refine ⟨u,v,huv,hM,hN,?_⟩
   intro he
   have hh := congrArg (fun q : Equiv.Perm (Remaining u v) => (q ⟨w,hwu,hwv⟩).val) he
   rw [crossMatching_mate,crossMatching_mate] at hh
   exact hd hh

end MatchingSurgery
end
end Holant.Pauli.ExoticKlein
