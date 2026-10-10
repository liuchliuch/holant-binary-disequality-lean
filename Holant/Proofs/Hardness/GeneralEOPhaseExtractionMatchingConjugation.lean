import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingOrder
import Holant.Proofs.Hardness.GeneralEOPhaseExtractionMatchingCap

/-! Any port transposition can be moved into the final two complete pairs by
an actual permutation of whole pairs. This is the finite matching-switch
geometry; it does not depend on tensor coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingConjugation
open Holant
namespace M
export GeneralEOPhaseExtractionMatchingNormalForm (liftPerm tailPerm liftPerm_zero liftPerm_succ)
end M
namespace O
export GeneralEOPhaseExtractionMatchingOrder (port port_val blockPerm blockPerm_port)
end O
namespace C
export GeneralEOPhaseExtractionMatchingCap (lastPerm lastPort lastPort_val)
end C
set_option backward.isDefEq.respectTransparency false

theorem liftPerm_swap {n : ℕ} (i j : Fin n) :
    M.liftPerm (Equiv.swap i j)=Equiv.swap i.succ j.succ := by
  apply Equiv.ext
  intro x
  refine Fin.cases ?_ (fun x => ?_) x
  · rw [M.liftPerm_zero]
    symm
    apply Equiv.swap_apply_of_ne_of_ne
    · intro h; have hv := congrArg Fin.val h; simp at hv
    · intro h; have hv := congrArg Fin.val h; simp at hv
  · rw [M.liftPerm_succ]
    simp only [Equiv.swap_apply_def,Fin.succ_inj]
    split_ifs <;> rfl

theorem lastPerm_swap (k : ℕ) (i j : Fin 4) :
    C.lastPerm k (Equiv.swap i j)=Equiv.swap (C.lastPort k i) (C.lastPort k j) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [GeneralEOPhaseExtractionMatchingCap.lastPerm,ih,
      GeneralEOPhaseExtractionMatchingNormalForm.tailPerm,liftPerm_swap,
      GeneralEOPhaseExtractionMatchingCap.lastPort]

/-- At most two selected pair indices fit in the last two pair positions. -/
theorem pairs_to_last (k : ℕ) (i j : Fin (k+2)) :
    ∃p : Equiv.Perm (Fin (k+2)),k≤(p i).val ∧ k≤(p j).val := by
  classical
  by_cases hij : i=j
  · subst j
    refine ⟨Equiv.swap i ⟨k,by omega⟩,?_,?_⟩ <;> simp
  let v : Fin 2→Fin (k+2) := ![i,j]
  let w : Fin 2→Fin (k+2) := ![⟨k,by omega⟩,⟨k+1,by omega⟩]
  have hv : Function.Injective v := by
    intro x y h
    fin_cases x <;> fin_cases y <;> simp_all [v]
  have hw : Function.Injective w := by
    intro x y h
    fin_cases x <;> fin_cases y
    all_goals first | rfl | have hh := congrArg Fin.val h; simp [w] at hh
  obtain ⟨p,hp⟩ := Equiv.Perm.exists_extending_pair v w hv hw
  refine ⟨p,?_,?_⟩
  · have hi : p i=⟨k,by omega⟩ := hp 0
    rw [hi]
  · have hj : p j=⟨k+1,by omega⟩ := hp 1
    rw [hj]
    change k≤k+1
    omega

/-- Conjugate any original-port swap into a permutation of the final four
ports. The conjugating permutation preserves the set of complete pairs. -/
theorem tail_swap (k : ℕ) (i j : Fin (2*k+4)) :
    ∃p : Equiv.Perm (Fin (k+2)),∃q : Equiv.Perm (Fin 4),
      (Equiv.swap i j).trans (O.blockPerm p)=(O.blockPerm p).trans (C.lastPerm k q) := by
  let a := (O.port (k+2)).symm i
  let b := (O.port (k+2)).symm j
  obtain ⟨p,hpa,hpb⟩ := pairs_to_last k a.1 b.1
  let r := O.blockPerm p
  have hi : i=O.port (k+2) (a.1,a.2) := ((O.port (k+2)).apply_symm_apply i).symm
  have hj : j=O.port (k+2) (b.1,b.2) := ((O.port (k+2)).apply_symm_apply j).symm
  have hir : 2*k≤(r i).val := by
    dsimp only [r]
    rw [hi,O.blockPerm_port,O.port_val]
    omega
  have hjr : 2*k≤(r j).val := by
    dsimp only [r]
    rw [hj,O.blockPerm_port,O.port_val]
    omega
  let u : Fin 4 := ⟨(r i).val-2*k,by have hh := (r i).isLt; omega⟩
  let v : Fin 4 := ⟨(r j).val-2*k,by have hh := (r j).isLt; omega⟩
  have hu : C.lastPort k u=r i := by
    apply Fin.ext
    rw [C.lastPort_val]
    change 2*k+((r i).val-2*k)=(r i).val
    omega
  have hv : C.lastPort k v=r j := by
    apply Fin.ext
    rw [C.lastPort_val]
    change 2*k+((r j).val-2*k)=(r j).val
    omega
  refine ⟨p,Equiv.swap u v,?_⟩
  rw [lastPerm_swap,hu,hv]
  apply Equiv.ext
  intro x
  exact (r.injective.swap_apply i j x).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionMatchingConjugation
