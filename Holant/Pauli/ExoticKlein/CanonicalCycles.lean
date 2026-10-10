import Holant.Pauli.ExoticKlein.OrbitCoordinates

/-! The cycles of two actual matchings, selected canonically from paired
alternating orbits. Every original port occurs exactly once. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open Equiv
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]
attribute [local instance] Classical.propDecidable

 def CycleHead (M N : Matching P r) :=
  {p : P // M.orbitHead N p = p ∧ p < M.orbitHead N (M.mate p)}

 instance (M N : Matching P r) : Fintype (M.CycleHead N) := by unfold CycleHead; infer_instance

 def CycleEdge (M N : Matching P r) := (c : M.CycleHead N) × Fin (M.orbitSet N c.val).card

 instance (M N : Matching P r) : Fintype (M.CycleEdge N) := inferInstanceAs (Fintype (Sigma _))

 instance (M N : Matching P r) : DecidableEq (M.CycleHead N) := by unfold CycleHead; infer_instance

 instance (M N : Matching P r) : DecidableEq (M.CycleEdge N) := by unfold CycleEdge; infer_instance

 def cyclePoint (M N : Matching P r) (e : M.CycleEdge N) : P := (M.orbitEquiv N e.1.val e.2).val

 theorem head_cyclePoint (M N : Matching P r) (e : M.CycleEdge N) :
    M.orbitHead N (M.cyclePoint N e) = e.1.val := by
  rw [← e.1.property.1]
  apply (M.orbitHead_eq_iff N _ _).mpr
  exact ((mem_orbitSet M N e.1.val _).mp (M.orbitEquiv N e.1.val e.2).property).symm

 theorem head_mate_cyclePoint (M N : Matching P r) (e : M.CycleEdge N) :
    M.orbitHead N (M.mate (M.cyclePoint N e)) = M.orbitHead N (M.mate e.1.val) := by
  apply (M.orbitHead_eq_iff N _ _).mpr
  apply (M.sameCycle_mate_iff N _ _).mpr
  exact ((mem_orbitSet M N e.1.val _).mp (M.orbitEquiv N e.1.val e.2).property).symm

 def cycleRoot (M N : Matching P r) (p : P) : P :=
  min (M.orbitHead N p) (M.orbitHead N (M.mate p))

@[simp] theorem cycleRoot_mate (M N : Matching P r) (p : P) :
    M.cycleRoot N (M.mate p) = M.cycleRoot N p := by simp [cycleRoot,min_comm]

 theorem cycleRoot_point (M N : Matching P r) (e : M.CycleEdge N) :
    M.cycleRoot N (M.cyclePoint N e) = e.1.val := by
  rw [cycleRoot,head_cyclePoint,head_mate_cyclePoint,min_eq_left (le_of_lt e.1.property.2)]

 def canonicalPort (M N : Matching P r) (q : M.CycleEdge N × Bool) : P :=
  if q.2 then M.mate (M.cyclePoint N q.1) else M.cyclePoint N q.1

 theorem cycleRoot_canonicalPort (M N : Matching P r) (q : M.CycleEdge N × Bool) :
    M.cycleRoot N (M.canonicalPort N q) = q.1.1.val := by
  rcases q with ⟨e,b⟩
  cases b <;> simp [canonicalPort,M.cycleRoot_point N]

 theorem cyclePoint_injective (M N : Matching P r) : Function.Injective (M.cyclePoint N) := by
  intro e f h
  have hc : e.1 = f.1 := Subtype.ext (by simpa only [head_cyclePoint] using congrArg (M.orbitHead N) h)
  cases e with | mk c i =>
    cases f with | mk d j =>
      dsimp at hc
      subst d
      have hij : i = j := (M.orbitEquiv N c.val).injective (Subtype.ext h)
      subst j
      rfl

 theorem canonicalPort_injective (M N : Matching P r) : Function.Injective (M.canonicalPort N) := by
  rintro ⟨e,b⟩ ⟨f,d⟩ h
  have hc : e.1.val = f.1.val := by
    simpa only [cycleRoot_canonicalPort] using congrArg (M.cycleRoot N) h
  cases b <;> cases d
  · exact Prod.ext (M.cyclePoint_injective N h) rfl
  · have hh := congrArg (M.orbitHead N) h
    change M.orbitHead N (M.cyclePoint N e) = M.orbitHead N (M.mate (M.cyclePoint N f)) at hh
    rw [head_cyclePoint,head_mate_cyclePoint,hc] at hh
    exact False.elim (ne_of_lt f.1.property.2 hh)
  · have hh := congrArg (M.orbitHead N) h
    change M.orbitHead N (M.mate (M.cyclePoint N e)) = M.orbitHead N (M.cyclePoint N f) at hh
    rw [head_cyclePoint,head_mate_cyclePoint,← hc] at hh
    exact False.elim (ne_of_lt e.1.property.2 hh.symm)
  · exact Prod.ext (M.cyclePoint_injective N (M.mate.injective h)) rfl

 theorem canonicalPort_surjective (M N : Matching P r) : Function.Surjective (M.canonicalPort N) := by
  intro p
  by_cases h : M.orbitHead N p < M.orbitHead N (M.mate p)
  · let c : M.CycleHead N := ⟨M.orbitHead N p,M.orbitHead_head N p,by
      simpa only [orbitHead_mate_head] using h⟩
    have hp : p ∈ M.orbitSet N c.val := (mem_orbitSet M N _ _).mpr (M.sameCycle_head N p).symm
    let i := (M.orbitEquiv N c.val).symm ⟨p,hp⟩
    refine ⟨(⟨c,i⟩,false),?_⟩
    exact congrArg Subtype.val ((M.orbitEquiv N c.val).apply_symm_apply ⟨p,hp⟩)
  · have h' : M.orbitHead N (M.mate p) < M.orbitHead N p :=
      lt_of_le_of_ne (le_of_not_gt h) (M.orbitHead_ne_mate N p).symm
    let c : M.CycleHead N := ⟨M.orbitHead N (M.mate p),M.orbitHead_head N (M.mate p),by
      simpa only [orbitHead_mate_head,mate_mate] using h'⟩
    have hp : M.mate p ∈ M.orbitSet N c.val := (mem_orbitSet M N _ _).mpr (M.sameCycle_head N (M.mate p)).symm
    let i := (M.orbitEquiv N c.val).symm ⟨M.mate p,hp⟩
    refine ⟨(⟨c,i⟩,true),?_⟩
    change M.mate ((M.orbitEquiv N c.val) i).val = p
    rw [show ((M.orbitEquiv N c.val) i).val = M.mate p from
      congrArg Subtype.val ((M.orbitEquiv N c.val).apply_symm_apply ⟨M.mate p,hp⟩),mate_mate]

 def canonicalPorts (M N : Matching P r) : (M.CycleEdge N × Bool) ≃ P :=
  Equiv.ofBijective (M.canonicalPort N) ⟨M.canonicalPort_injective N,M.canonicalPort_surjective N⟩

 theorem canonicalPorts_mate (M N : Matching P r) (e : M.CycleEdge N) (b : Bool) :
    M.mate (M.canonicalPorts N (e,b)) = M.canonicalPorts N (e,!b) := by
  change M.mate (M.canonicalPort N (e,b)) = M.canonicalPort N (e,!b)
  cases b <;> simp [canonicalPort]

 theorem card_cycleEdge (M N : Matching P r) : Fintype.card (M.CycleEdge N) = r := by
  have h := Fintype.card_congr (M.canonicalPorts N)
  rw [Fintype.card_prod,Fintype.card_bool,M.port_card] at h
  omega

end Matching
end
end Holant.Pauli.ExoticKlein
