import Holant.Proofs.Hardness.BinaryCSPProgrammeRepeat

/-! Literal apex rows, with a separate aligned list controlling physical port
reversal. No extra signature or unary weight is inserted in the palette. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingRaw
open BinaryCSPProgrammeCore

def apexRaw (r : Raw) : Raw :=
  ⟨r.variables+1,r.edges.flatMap (fun e=>[(e.1+1,0),(e.2+1,0),(e.1+1,e.2+1)]),[]⟩

def polarities (r : Raw) : List Bool := r.edges.flatMap (fun _=>[false,false,true])

def expanded (r : Raw) (k : ℕ) : Raw := BinaryCSPProgrammeRepeat.expand (apexRaw r) k

def expandedPolarities (r : Raw) (k : ℕ) : List Bool :=
  (polarities r).flatMap (List.replicate (k+1))

@[simp] theorem apex_variables (r : Raw) : (apexRaw r).variables=r.variables+1 := rfl
@[simp] theorem apex_signs (r : Raw) : (apexRaw r).signs=[] := rfl
@[simp] theorem apex_edges_length (r : Raw) : (apexRaw r).edges.length=r.edges.length*3 := by
  simp [apexRaw,List.length_flatMap,List.sum_replicate]
@[simp] theorem polarities_length (r : Raw) : (polarities r).length=r.edges.length*3 := by
  simp [polarities,List.length_flatMap,List.sum_replicate]
@[simp] theorem expanded_edges_length (r : Raw) (k : ℕ) :
    (expanded r k).edges.length=r.edges.length*3*(k+1) := by simp [expanded]
@[simp] theorem expanded_polarities_length (r : Raw) (k : ℕ) :
    (expandedPolarities r k).length=(expanded r k).edges.length := by
  simp [expandedPolarities,List.length_flatMap,List.sum_replicate]

theorem apex_valid (r : Raw) (hr : r.WellFormed) : (apexRaw r).WellFormed := by
  refine ⟨?_,by simp [apexRaw]⟩
  intro e he
  obtain ⟨old,hold,he⟩ := List.mem_flatMap.mp he
  have h := hr.1 old hold
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl <;> dsimp only [apexRaw] <;> omega

theorem expanded_valid (r : Raw) (hr : r.WellFormed) (k : ℕ) :
    (expanded r k).WellFormed := BinaryCSPProgrammeRepeat.repeat_valid _ (apex_valid r hr) k

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryIsingRaw
