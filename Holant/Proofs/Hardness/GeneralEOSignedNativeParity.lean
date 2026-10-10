import Holant.Proofs.Hardness.GeneralEOSignedParityAssignments
import Holant.Proofs.Hardness.GeneralEOPairedCSPCycles

/-! Arbitrary closed native-X networks, including loops and parallel edges,
are converted to their literal edge-variable parity constraints. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeParity
open Holant Holant.Tractable
open scoped BigOperators
namespace C
export GeneralEOPairedCSPCycles (assignments edge_product Covers compress closedPorts)
end C
namespace D
export GeneralEOSignedParityComponents (Links Consistent Good scope signs reconstruct assignment_sum inconsistent_sum_zero)
end D
namespace L
export Holant.LocalDrafts.Tractability.EOEvaluation.PairLift (Compatible word_compress)
end L
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option Elab.async false
variable (S : NetworkShape 0)

def port (v : Fin S.vertices) (j : Fin (S.arity v)) : Fin S.edges × Bool :=
  (C.closedPorts S.edges).symm (S.ports ⟨v,j⟩)
def row (a : Fin S.edges → Bool) (v : Fin S.vertices) : Fin (S.arity v) → Bool :=
  fun j => Bool.xor (a (port S v j).1) (port S v j).2

theorem assignment_native (a : Fin S.edges → Bool) (v : Fin S.vertices) :
    S.assignment Fin.elim0 (fun q => if q.2 then !(a q.1) else a q.1) v = row S a v := by
  funext j
  unfold NetworkShape.assignment row port
  cases h : S.ports ⟨v,j⟩ with
  | inl z => exact Fin.elim0 z
  | inr q =>
    rcases q with ⟨e,b⟩
    cases b <;> simp [C.closedPorts]

theorem native_sum {K : Type*} [CommSemiring K] (N : Network K 0)
    (he : ∀e,N.edge e=Signature.disequality) :
    N.denote Fin.elim0 = ∑a : Fin N.shape.edges → Bool,
      ∏v : Fin N.shape.vertices,N.vertex v (row N.shape a v) := by
  classical
  unfold Network.denote
  simp_rw [he]
  rw [←(C.assignments N.shape.edges).symm.sum_comp,Fintype.sum_prod_type]
  simp only [C.assignments,Equiv.coe_fn_symm_mk,Bool.false_eq_true,ite_false,ite_true,C.edge_product]
  simp only [mul_ite,mul_one,mul_zero,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.prod_congr rfl
  intro v _
  rw [assignment_native]

variable (P : (v : Fin S.vertices) → OrientedPerfectPairing (S.arity v))
def link (v : Fin S.vertices) (j : Fin (P v).count) :
    (Fin S.edges × Fin S.edges) × Bool :=
  let a := port S v ((P v).ports (j,false))
  let b := port S v ((P v).ports (j,true))
  ((a.1,b.1),Bool.xor true (Bool.xor a.2 b.2))
def links : D.Links S.edges :=
  (List.finRange S.vertices).flatMap (fun v => List.ofFn (link S P v))

local instance (a : Fin S.edges → Bool) : Decidable (D.Consistent (links S P) a) :=
  Classical.propDecidable _

theorem link_mem (v : Fin S.vertices) (j : Fin (P v).count) : link S P v j ∈ links S P :=
  List.mem_flatMap.mpr ⟨v,List.mem_finRange _,List.mem_ofFn.mpr ⟨j,rfl⟩⟩

private theorem bits (a b s t : Bool) :
    Bool.xor a s ≠ Bool.xor b t ↔ a=Bool.xor b (Bool.xor true (Bool.xor s t)) := by
  cases a <;> cases b <;> cases s <;> cases t <;> decide

theorem consistent_iff (a : Fin S.edges → Bool) :
    D.Consistent (links S P) a ↔ ∀v,L.Compatible (P v) (row S a v) := by
  constructor
  · intro h v j
    have hh := h (link S P v j) (link_mem S P v j)
    change Bool.xor (a (port S v ((P v).ports (j,false))).1)
        (port S v ((P v).ports (j,false))).2 ≠
      Bool.xor (a (port S v ((P v).ports (j,true))).1)
        (port S v ((P v).ports (j,true))).2
    exact (bits _ _ _ _).mpr hh
  · intro h q hq
    obtain ⟨v,hv,hq⟩ := List.mem_flatMap.mp hq
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hq
    exact (bits _ _ _ _).mp (h v j)

def compressedInput (a : Fin S.edges → Bool) (v : Fin S.vertices) : Fin (P v).count → Bool :=
  fun j => row S a v ((P v).ports (j,false))

def weight {K : Type*} [CommSemiring K] (f : (v : Fin S.vertices) → Signature K (S.arity v))
    (a : Fin S.edges → Bool) : K :=
  ∏v,C.compress (P v) (f v) (compressedInput S P a v)

theorem vertex_value {K : Type*} [Zero K]
    (f : (v : Fin S.vertices) → Signature K (S.arity v))
    (hf : ∀v,C.Covers (P v) (f v)) (a : Fin S.edges → Bool) (v : Fin S.vertices) :
    f v (row S a v) = if L.Compatible (P v) (row S a v) then
      C.compress (P v) (f v) (compressedInput S P a v) else 0 := by
  classical
  by_cases h : L.Compatible (P v) (row S a v)
  · rw [ite_eq_left h]
    exact congrArg (f v) (L.word_compress (P v) (row S a v) h).symm
  · rw [ite_eq_right h]
    by_contra hn
    exact h (hf v _ hn)

theorem product_value {K : Type*} [CommSemiring K]
    (f : (v : Fin S.vertices) → Signature K (S.arity v))
    (hf : ∀v,C.Covers (P v) (f v)) (a : Fin S.edges → Bool) :
    (∏v,f v (row S a v)) =
      if D.Consistent (links S P) a then weight S P f a else 0 := by
  classical
  by_cases h : D.Consistent (links S P) a
  · rw [ite_eq_left h]
    apply Finset.prod_congr rfl
    intro v _
    rw [vertex_value S P f hf,ite_eq_left ((consistent_iff S P a).mp h v)]
  · rw [ite_eq_right h]
    have hn : ¬∀v,L.Compatible (P v) (row S a v) := fun hh => h ((consistent_iff S P a).mpr hh)
    obtain ⟨v,hv⟩ := not_forall.mp hn
    apply Finset.prod_eq_zero (Finset.mem_univ v)
    rw [vertex_value S P f hf,ite_eq_right hv]

theorem denote_parity {K : Type*} [CommSemiring K] (N : Network K 0)
    (P : (v : Fin N.shape.vertices) → OrientedPerfectPairing (N.shape.arity v))
    (he : ∀e,N.edge e=Signature.disequality) (hf : ∀v,C.Covers (P v) (N.vertex v)) :
    N.denote Fin.elim0 = ∑a : Fin N.shape.edges → Bool,
      if D.Consistent (links N.shape P) a then weight N.shape P N.vertex a else 0 := by
  classical
  rw [native_sum N he]
  apply Finset.sum_congr rfl
  intro a _
  exact product_value N.shape P N.vertex hf a

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedNativeParity
