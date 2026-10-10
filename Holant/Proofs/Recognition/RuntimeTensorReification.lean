import Holant.Proofs.Recognition.RuntimeTensorValidation
import Mathlib.Algebra.BigOperators.Fin

/-! Proof-side interpretation of a physically validated runtime port catalogue.
The mathematical equivalence is reconstructed only from the actual candidate's
bounded entries, size sum, and all-port coverage. No typed partition is input
to the candidate programme. Algebraic row compilation remains separate. -/
namespace Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorReification
open Holant Holant.Tractable
open Holant.LocalDrafts.MainChain.TransformRecognition
open UniformTensorWitnessBranch (Metadata)
open RuntimeTensorCatalogue RuntimeTensorValidation
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ} (m : Metadata) (generated : m ∈ catalogue n)
variable (oneHot : Bool) (accepted : valid (oneHot,n,m)=true)

abbrev count := m.1.length
abbrev arity : Fin (count m) → ℕ := m.1.get

include accepted in
theorem size_sum : ∑i : Fin (count m),arity m i=n := by
  have h := ((valid_correct oneHot n m).mp accepted).1
  simpa only [arity,←List.sum_ofFn,List.ofFn_get] using h

def portFunction (i : Fin n) : Fin n :=
  ⟨m.2.1.get (Fin.cast (generated_bounds n m generated).2.2.1.symm i),
    (generated_bounds n m generated).2.2.2.1 _ (List.get_mem _ _)⟩

include accepted in
theorem port_surjective : Function.Surjective (portFunction m generated) := by
  intro j
  have hm : j.val∈m.2.1 := ((valid_correct oneHot n m).mp accepted).2.2 j.val j.isLt
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hm
  refine ⟨Fin.cast (generated_bounds n m generated).2.2.1 i,?_⟩
  apply Fin.ext
  simpa only [portFunction,Fin.cast_cast,Fin.cast_refl,id_eq] using hi

/-- The inverse is proof-side only; the physical row programme uses the
forward raw port lookups. -/
def portEquiv : Fin n ≃ Fin n :=
  Equiv.ofBijective (portFunction m generated)
    (port_surjective m generated oneHot accepted).bijective_of_finite

def blockPorts : (Σ i : Fin (count m), Fin (arity m i)) ≃ Fin n :=
  (finSigmaFinEquiv.trans (finCongr (size_sum m oneHot accepted))).trans
    (portEquiv m generated oneHot accepted)

/-- Literal raw port lookup at the canonical block offset. This is the value
that a runtime polynomial row compiler must compute. -/
theorem blockPorts_raw (i : Fin (count m)) (j : Fin (arity m i)) :
    (blockPorts m generated oneHot accepted ⟨i,j⟩).val =
      m.2.1.get (Fin.cast (generated_bounds n m generated).2.2.1.symm
        (Fin.cast (size_sum m oneHot accepted) (finSigmaFinEquiv ⟨i,j⟩))) := rfl

include accepted in
theorem block_allowed (i : Fin (count m)) : allowed oneHot (arity m i)=true :=
  ((valid_correct oneHot n m).mp accepted).2.1 _ (List.get_mem _ _)

def pivot : Fin n → Bool := fun i =>
  m.2.2.get (Fin.cast (generated_bounds n m generated).2.2.2.2.symm i)

def arityShape (accepted : valid (false,n,m)=true) : TensorDecision.Shape n :=
  ⟨⟨count m,Nat.lt_succ_of_le (generated_bounds n m generated).1⟩,
    (fun i => ⟨arity m i,by
      have hi := (allowed_false (arity m i)).mp (block_allowed m false accepted i)
      rcases hi with h | h <;> omega⟩),
    blockPorts m generated false accepted,
    fun i => (allowed_false (arity m i)).mp (block_allowed m false accepted i)⟩

def matchingShape (accepted : valid (true,n,m)=true) : TensorDecisionStable.Shape n :=
  ⟨⟨count m,Nat.lt_succ_of_le (generated_bounds n m generated).1⟩,
    (fun i => ⟨arity m i,Nat.lt_succ_of_le
      ((generated_bounds n m generated).2.1 _ (List.get_mem _ _))⟩),
    blockPorts m generated true accepted,
    fun i => (allowed_true (arity m i)).mp (block_allowed m true accepted i)⟩

end
end Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeTensorReification
