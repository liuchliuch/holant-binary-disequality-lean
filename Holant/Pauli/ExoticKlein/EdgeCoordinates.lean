import Holant.Pauli.ExoticKlein.CycleSuccessor

/-! Exact original edge IDs and orientation bits for any paired port coordinates. -/
namespace Holant.Pauli.ExoticKlein
noncomputable section
open Equiv
namespace Matching
variable {P I : Type*} {r : ℕ}

structure PairCoordinates (M : Matching P r) (I : Type*) where
  ports : (I × Bool) ≃ P
  paired : ∀ i b, M.mate (ports (i,b)) = ports (i,!b)

namespace PairCoordinates
variable {M : Matching P r} (C : M.PairCoordinates I)

def edge (i : I) : Fin r := (M.ports.symm (C.ports (i,false))).1

def reverse (i : I) : Bool := (M.ports.symm (C.ports (i,false))).2

 theorem ports_false (i : I) : C.ports (i,false) = M.ports (C.edge i,C.reverse i) := by
  exact (M.ports.apply_symm_apply (C.ports (i,false))).symm

 theorem ports_true (i : I) : C.ports (i,true) = M.ports (C.edge i,!(C.reverse i)) := by
  have h := C.paired i false
  simp only [Bool.not_false] at h
  rw [← h,C.ports_false,M.mate_port]

 theorem edge_injective : Function.Injective C.edge := by
  intro i j h
  by_cases hr : C.reverse i = C.reverse j
  · have hp : C.ports (i,false) = C.ports (j,false) := by rw [C.ports_false,C.ports_false,h,hr]
    exact congrArg Prod.fst (C.ports.injective hp)
  · have hr' : C.reverse i = !(C.reverse j) := by
      cases hi : C.reverse i <;> cases hj : C.reverse j <;> simp_all
    have hp : C.ports (i,false) = C.ports (j,true) := by rw [C.ports_false,C.ports_true,h,hr']
    exact False.elim (Bool.false_ne_true (congrArg Prod.snd (C.ports.injective hp)))

 theorem edge_surjective : Function.Surjective C.edge := by
  intro e
  obtain ⟨⟨i,b⟩,hi⟩ := C.ports.surjective (M.ports (e,false))
  refine ⟨i,?_⟩
  cases b
  · rw [C.ports_false] at hi
    exact congrArg Prod.fst (M.ports.injective hi)
  · rw [C.ports_true] at hi
    exact congrArg Prod.fst (M.ports.injective hi)

 def edges : I ≃ Fin r := Equiv.ofBijective C.edge ⟨C.edge_injective,C.edge_surjective⟩

@[simp] theorem edges_apply (i : I) : C.edges i = C.edge i := rfl

 theorem dual_entry (a : Fin r → Label) (x : P → Bool) (i : I) :
    dual (a (C.edges i)) (x (M.ports (C.edges i,false))) (x (M.ports (C.edges i,true))) =
    oriented (C.reverse i) (dual (a (C.edges i))) (x (C.ports (i,false))) (x (C.ports (i,true))) := by
  change dual (a (C.edge i)) (x (M.ports (C.edge i,false))) (x (M.ports (C.edge i,true))) = _
  rw [C.ports_false,C.ports_true]
  cases hi : C.reverse i <;> simp only [oriented,hi,edges_apply,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,Kernel.transpose]

 theorem tensor_entry (a : Fin r → Label) (x : P → Bool) (i : I) :
    E (a (C.edges i)) (x (M.ports (C.edges i,false))) (x (M.ports (C.edges i,true))) =
    oriented (C.reverse i) (E (a (C.edges i))) (x (C.ports (i,false))) (x (C.ports (i,true))) := by
  change E (a (C.edge i)) (x (M.ports (C.edge i,false))) (x (M.ports (C.edge i,true))) = _
  rw [C.ports_false,C.ports_true]
  cases hi : C.reverse i <;> simp only [oriented,hi,edges_apply,Bool.false_eq_true,ite_false,ite_true,Bool.not_false,Bool.not_true,Kernel.transpose]

end PairCoordinates

variable [Fintype P] [LinearOrder P]

def mCoordinates (M N : Matching P r) : M.PairCoordinates (M.CycleEdge N) :=
  ⟨M.canonicalPorts N,M.canonicalPorts_mate N⟩

def nCoordinates (M N : Matching P r) : N.PairCoordinates (M.CycleEdge N) :=
  ⟨M.canonicalNPorts N,M.canonicalNPorts_mate N⟩

end Matching
end
end Holant.Pauli.ExoticKlein
