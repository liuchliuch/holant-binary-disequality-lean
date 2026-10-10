import Holant.Pauli.ExoticKlein.CanonicalCycles
import Mathlib.Logic.Equiv.Fin.Rotate

namespace Holant.Pauli.ExoticKlein
noncomputable section
open Equiv
namespace Matching
variable {P : Type*} {r : ℕ} [Fintype P] [LinearOrder P]

 theorem orbitEquiv_rotate (M N : Matching P r) (p : P)
    (i : Fin (M.orbitSet N p).card) :
    (M.orbitEquiv N p (finRotate _ i)).val =
      (M.alternating N) (M.orbitEquiv N p i).val := by
  rw [orbitEquiv_val,orbitEquiv_val]
  have hc : 0 < (M.orbitSet N p).card := Finset.card_pos.mpr (M.orbitSet_nonempty N p)
  letI : NeZero (M.orbitSet N p).card := ⟨Nat.ne_of_gt hc⟩
  rw [finRotate_apply]
  by_cases hi : i.val+1 < (M.orbitSet N p).card
  · have he : ((i+1 : Fin (M.orbitSet N p).card)).val = i.val+1 := by
      exact Fin.val_add_one_of_lt' hi
    rw [he,pow_succ']
    rfl
  · have he : ((i+1 : Fin (M.orbitSet N p).card)).val = 0 := by
      have hi' : i.val+1 = (M.orbitSet N p).card := by omega
      simp only [Fin.val_add,Fin.val_one',Nat.add_mod_mod,hi',Nat.mod_self]
    rw [he]
    have hi' : i.val+1 = (M.orbitSet N p).card := by omega
    have hh := (M.isCycleOn_orbitSet N p).pow_card_apply (M.self_mem_orbitSet N p)
    rw [← hi',pow_succ'] at hh
    exact hh.symm

 def cycleNext (M N : Matching P r) : Equiv.Perm (M.CycleEdge N) where
  toFun e := ⟨e.1,finRotate _ e.2⟩
  invFun e := ⟨e.1,(finRotate _).symm e.2⟩
  left_inv e := by
    cases e with | mk c i =>
      dsimp
      rw [Equiv.symm_apply_apply]
  right_inv e := by
    cases e with | mk c i =>
      dsimp
      rw [Equiv.apply_symm_apply]

 theorem cyclePoint_next (M N : Matching P r) (e : M.CycleEdge N) :
    M.cyclePoint N (M.cycleNext N e) = M.alternating N (M.cyclePoint N e) :=
  M.orbitEquiv_rotate N e.1.val e.2

 theorem canonicalPorts_Nmate (M N : Matching P r) (e : M.CycleEdge N) :
    N.mate (M.canonicalPorts N (e,true)) = M.canonicalPorts N (M.cycleNext N e,false) := by
  change N.mate (M.mate (M.cyclePoint N e)) = M.cyclePoint N (M.cycleNext N e)
  exact (M.cyclePoint_next N e).symm

 def nextPortEquiv (M N : Matching P r) : (M.CycleEdge N × Bool) ≃ (M.CycleEdge N × Bool) where
  toFun q := if q.2 then (M.cycleNext N q.1,false) else (q.1,true)
  invFun q := if q.2 then (q.1,false) else ((M.cycleNext N).symm q.1,true)
  left_inv q := by rcases q with ⟨e,b⟩; cases b <;> simp
  right_inv q := by rcases q with ⟨e,b⟩; cases b <;> simp

 def canonicalNPorts (M N : Matching P r) : (M.CycleEdge N × Bool) ≃ P :=
  (M.nextPortEquiv N).trans (M.canonicalPorts N)

@[simp] theorem canonicalNPorts_false (M N : Matching P r) (e : M.CycleEdge N) :
    M.canonicalNPorts N (e,false) = M.canonicalPorts N (e,true) := rfl

@[simp] theorem canonicalNPorts_true (M N : Matching P r) (e : M.CycleEdge N) :
    M.canonicalNPorts N (e,true) = M.canonicalPorts N (M.cycleNext N e,false) := rfl

 theorem canonicalNPorts_mate (M N : Matching P r) (e : M.CycleEdge N) (b : Bool) :
    N.mate (M.canonicalNPorts N (e,b)) = M.canonicalNPorts N (e,!b) := by
  cases b
  · exact M.canonicalPorts_Nmate N e
  · simpa only [canonicalNPorts_true,canonicalNPorts_false,Bool.not_true,mate_mate] using
      congrArg N.mate (M.canonicalPorts_Nmate N e).symm

end Matching
end
end Holant.Pauli.ExoticKlein
