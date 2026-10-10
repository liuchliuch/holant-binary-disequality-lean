import Holant.Certificates.AffineEndpoint.Phases
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.NodupEquivFin

/-! Computable integer phase codes. Coverage follows from explicit digit
round trips, not from enumerating arbitrary phase functions as a premise. -/
namespace Holant.Certificates.AffineEndpoint
open Holant Holant.Tractable
set_option backward.isDefEq.respectTransparency false

 def mixedPairList (d : ℕ) : List (MixedPair d) :=
  (List.finRange d).flatMap (fun j => (List.finRange d).filterMap
    (fun k => if h : j<k then some ⟨(j,k),h⟩ else none))

 theorem mem_mixedPairList {d : ℕ} (p : MixedPair d) : p∈mixedPairList d := by
  apply List.mem_flatMap.mpr
  refine ⟨p.val.1,by simp,?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨p.val.2,by simp,?_⟩
  simp [p.property]

 def mixedPairPosition {d : ℕ} (p : MixedPair d) : Fin (mixedPairList d).length :=
  ⟨(mixedPairList d).idxOf p,List.idxOf_lt_length_iff.mpr (mem_mixedPairList p)⟩

 theorem mixedPair_at_position {d : ℕ} (p : MixedPair d) :
    (mixedPairList d).get (mixedPairPosition p)=p := by
  exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (mem_mixedPairList p))

 def boolCode (b : Bool) : Fin 2 := if b then 1 else 0
 def codeBool (i : Fin 2) : Bool := decide (i=1)

 theorem codeBool_boolCode (b : Bool) : codeBool (boolCode b)=b := by cases b <;> decide

 def phaseCodeCount (d : ℕ) : ℕ := 4^d*2^(mixedPairList d).length

 def phaseDecode (d : ℕ) (c : Fin (phaseCodeCount d)) : PhaseParameters d :=
  let p : Fin (4^d)×Fin (2^(mixedPairList d).length) := finProdFinEquiv.symm c
  (finFunctionFinEquiv.symm p.1,
    fun jk => codeBool (finFunctionFinEquiv.symm p.2 (mixedPairPosition jk)))

 def phaseEncode {d : ℕ} (p : PhaseParameters d) : Fin (phaseCodeCount d) :=
  finProdFinEquiv (finFunctionFinEquiv p.1,
    finFunctionFinEquiv (fun i : Fin (mixedPairList d).length => boolCode (p.2 ((mixedPairList d).get i))))

 theorem phaseDecode_encode {d : ℕ} (p : PhaseParameters d) : phaseDecode d (phaseEncode p)=p := by
  simp only [phaseDecode,phaseEncode,Equiv.symm_apply_apply]
  apply Prod.ext
  · rfl
  · funext jk
    change codeBool (boolCode (p.2 ((mixedPairList d).get (mixedPairPosition jk)))) = p.2 jk
    rw [mixedPair_at_position,codeBool_boolCode]

 theorem phaseDecode_surjective (d : ℕ) : Function.Surjective (phaseDecode d) :=
  fun p => ⟨phaseEncode p,phaseDecode_encode p⟩

 theorem phase_code_counts : phaseCodeCount 0=1 ∧ phaseCodeCount 1=4 ∧ phaseCodeCount 2=32 ∧
    phaseCodeCount 3=512 ∧ phaseCodeCount 4=16384 := by decide +kernel

end Holant.Certificates.AffineEndpoint
