import Holant.Proofs.Hardness.BinaryIsingCorrectness
import Holant.Proofs.Hardness.BinaryCSPProgrammeSigned

/-! The unsigned NAND target of the signed-star/circuit programme is precisely
the independent-set source of the Ising programme, on the identical raw codec. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingNand
open Holant Holant.Algebraic Holant.Complexity BinaryCSPProgrammeCore
open scoped BigOperators
namespace P
export BinaryCSPProgrammeValidated (Input inputEncoding)
end P
namespace I
export BinaryIsingProgramme (independentCount independentControlled validQueryEncoding validQueryValue)
end I
namespace Q
export BinaryIsingQuery (left right)
end Q
namespace V
export BinaryCSPProgrammeValue (assignment weight value)
end V
namespace G
export BinaryThreeSupportGates (nand)
end G
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
local instance (p : Prop) : Decidable p := Classical.propDecidable p

omit [Algebra ℚ K] in
theorem weight_eq (r : P.Input) (x : Fin r.val.variables→Bool) :
    V.weight (G.nand (K:=K)) r.val x=
      if EOBinaryPlaneIsing.Independent (Q.left r.val r.property) (Q.right r.val r.property) x
        then 1 else 0 := by
  classical
  have hp : V.weight (G.nand (K:=K)) r.val x=
      ∏i : Fin r.val.edges.length,G.nand (K:=K) (x (Q.left r.val r.property i))
        (x (Q.right r.val r.property i)) := by
    unfold V.weight
    rw [←List.prod_ofFn]
    congr 1
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hin : i<r.val.edges.length := by simpa using hi
      let v : Fin r.val.edges.length := ⟨i,hin⟩
      have bounds := r.property.1 _ (List.get_mem r.val.edges v)
      simp only [List.getElem_map,List.getElem_ofFn]
      have hl : V.assignment r.val x (r.val.edges.get v).1=x (Q.left r.val r.property v) := by
        unfold V.assignment
        rw [List.getD_eq_getElem _ _ (by simpa using bounds.1)]
        simp only [List.getElem_ofFn]
        rfl
      have hr : V.assignment r.val x (r.val.edges.get v).2=x (Q.right r.val r.property v) := by
        unfold V.assignment
        rw [List.getD_eq_getElem _ _ (by simpa using bounds.2)]
        simp only [List.getElem_ofFn]
        rfl
      simpa [v,List.get_eq_getElem] using congrArg₂ (G.nand (K:=K)) hl hr
  rw [hp]
  by_cases h : EOBinaryPlaneIsing.Independent (Q.left r.val r.property) (Q.right r.val r.property) x
  · rw [ite_eq_left h]
    apply Finset.prod_eq_one
    intro i _
    simp [G.nand,Bool.and_eq_true,h i]
  · rw [ite_eq_right h]
    simp only [EOBinaryPlaneIsing.Independent,not_forall,not_not] at h
    obtain ⟨i,hi,hj⟩ := h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [G.nand,hi,hj])

omit [Algebra ℚ K] in
theorem target_eq (r : P.Input) :
    BinaryCSPProgrammeSigned.targetValue (K:=K) r=I.independentCount (K:=K) r := by
  classical
  change V.value (G.nand (K:=K)) r.val=_
  simp only [V.value,I.independentCount,EOBinaryPlaneIsing.independentCount,
    Nat.cast_sum,Nat.cast_ite,Nat.cast_one,Nat.cast_zero]
  exact Finset.sum_congr rfl (fun x _=>weight_eq r x)

variable (F : FixedField K d) (p q : K)

def controlled (hp : p≠0) (hq : q≠0) (hr : ∀j,0<j→(q/p)^(2*j)≠1) :
    LengthControlledOracleReduction P.inputEncoding F.encoding I.validQueryEncoding F.encoding
      (BinaryCSPProgrammeSigned.targetValue (K:=K)) (I.validQueryValue p q) where
  reduction := {
    machine := (I.independentControlled F p q hp hq hr).reduction.machine
    time := (I.independentControlled F p q hp hq hr).reduction.time
    correct oracle ho r := by
      rw [target_eq]
      exact (I.independentControlled F p q hp hq hr).reduction.correct oracle ho r }
  targetOutput := (I.independentControlled F p q hp hq hr).targetOutput
  queryBound := (I.independentControlled F p q hp hq hr).queryBound
  safeQuery := (I.independentControlled F p q hp hq hr).safeQuery

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingNand
