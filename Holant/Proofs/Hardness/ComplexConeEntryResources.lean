import Holant.Proofs.Hardness.ComplexConeEntry

/-! Original-row templates for all six cone-entry choices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntry
open Holant Holant.Complexity FixedGadgetSubstitution
variable {K : Type} [Field K]

def labels (a b c : K) (step : Bool) (i : Fin 3) :
    Labelling (network a b c step i).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by cases step <;> fin_cases i <;> fin_cases v <;> rfl
  edge _ := 0

abbrev template (a b c : K) (step : Bool) (i : Fin 3) := (labels a b c step i).template

theorem valid (a b c : K) (step : Bool) (i : Fin 3) :
    (template a b c step i).WellFormed 1 1 (fun _=>4) := (labels a b c step i).wellFormed

theorem counts (a b c : K) (step : Bool) (i : Fin 3) :
    (template a b c step i).vertices.length=(if step then 2 else 1) ∧
    (template a b c step i).edges.length=(if step then 2 else 0) := by
  cases step <;> fin_cases i <;> exact ⟨rfl,rfl⟩

theorem template_denote (a b c : K) (step : Bool) (i : Fin 3) :
    ((template a b c step i).network (valid a b c step i)
      (fun _ : Fin 1=>S.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
      S.original (outputA a b c step i) (outputB a b c step i) (outputC a b c step i) := by
  rw [←denote]
  apply Labelling.denote_template_of_labels (labels a b c step i) _ _
    (network a b c step i).vertex (network a b c step i).edge
  · intro v x; cases step <;> fin_cases i <;> fin_cases v <;> rfl
  · intro e x y; cases step <;> fin_cases i <;> fin_cases e <;> rfl

/-- Exact original-vertex order and all boundary/edge incidences. -/
def rows (step : Bool) (i : Fin 3) : List (ℕ × List (ℕ ⊕ (ℕ × Bool))) :=
  if step then
    ![[(0,[.inl 0,.inr (1,false),.inl 3,.inr (0,false)]),
       (0,[.inr (1,true),.inl 2,.inr (0,true),.inl 1])],
      [(0,[.inl 0,.inl 3,.inr (0,false),.inr (1,false)]),
       (0,[.inr (1,true),.inr (0,true),.inl 1,.inl 2])],
      [(0,[.inl 0,.inr (0,false),.inr (1,false),.inl 3]),
       (0,[.inr (1,true),.inl 1,.inl 2,.inr (0,true)])]] i
  else
    ![[(0,[.inl 0,.inl 1,.inl 2,.inl 3])],
      [(0,[.inl 0,.inl 2,.inl 3,.inl 1])],
      [(0,[.inl 0,.inl 3,.inl 1,.inl 2])]] i

theorem records (a b c : K) (step : Bool) (i : Fin 3) :
    (template a b c step i).boundary=4 ∧
    (template a b c step i).vertices=rows step i ∧
    (template a b c step i).edges=(if step then [0,0] else []) := by
  cases step <;> fin_cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem original_occurrences (a b c : K) (step : Bool) (i : Fin 3) :
    ((template a b c step i).vertices.filter (fun row=>row.1=0)).length=
      (if step then 2 else 1) := by
  cases step <;> fin_cases i <;> rfl

/-- The chosen template is over the original singleton dictionary and native X. -/
theorem selected_template (a b c : ℂ) (h : AllNZ a b c) :
    let d := data a b c h
    ((template a b c d.step d.choice).network (valid a b c d.step d.choice)
      (fun _ : Fin 1=>S.original a b c) (fun _ : Fin 1=>Signature.disequality)).denote=
      S.original (outputA a b c d.step d.choice) (outputB a b c d.step d.choice)
        (outputC a b c d.step d.choice) := template_denote a b c _ _

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexConeEntry
