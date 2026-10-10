import Holant.Certificates.NormalizedDihedralQ6.Data

/-! Exact bijection from the source's three residual matchings, distinguished
fixed-edge choice, and three phase bits to the 48 finite sector records. -/
namespace Holant.Certificates.NormalizedDihedralQ6

abbrev SourceSector := Fin 3 × Bool × Bool × Bool × Bool

def residualMatching : Fin 3 → Pair × Pair :=
  ![((2,3),(4,5)),((2,4),(3,5)),((2,5),(3,4))]

def sourceEdge (d : Fin 3 × Bool) : Fin 6 :=
  if d.2 then ⟨5-d.1.val,by omega⟩ else ⟨d.1.val,by have := d.1.isLt; omega⟩
def edgeSource (e : Fin 6) : Fin 3 × Bool :=
  if h : e.val < 3 then (⟨e.val,h⟩,false)
  else (⟨5-e.val,by have := e.isLt; omega⟩,true)

def sourceEdgeEquiv : (Fin 3 × Bool) ≃ Fin 6 where
  toFun := sourceEdge
  invFun := edgeSource
  left_inv d := by rcases d with ⟨i,b⟩; fin_cases i <;> cases b <;> decide
  right_inv e := by fin_cases e <;> decide

/-- Both edges keep their canonical increasing endpoint order. -/
theorem source_edges_exact (i : Fin 3) (fixed : Bool) :
    fixedEdge (sourceEdge (i,fixed)) = (if fixed then (residualMatching i).2 else (residualMatching i).1) ∧
      varyingEdge (sourceEdge (i,fixed)) = (if fixed then (residualMatching i).1 else (residualMatching i).2) := by
  fin_cases i <;> cases fixed <;> decide

def sourceSectorEquiv : SourceSector ≃ Sector :=
  (Equiv.prodAssoc (Fin 3) Bool (Bool × Bool × Bool)).symm.trans
    (Equiv.prodCongr sourceEdgeEquiv (Equiv.refl _))

@[simp] theorem sourceSectorEquiv_apply (i : Fin 3) (fixed a b o : Bool) :
    sourceSectorEquiv (i,fixed,a,b,o) = (sourceEdge (i,fixed),a,b,o) := rfl

/-- Distinguishing either edge is a real labelled choice, not a quotient. -/
theorem sector_card : Fintype.card Sector = 48 := by simp [Sector]
theorem sourceSector_card : Fintype.card SourceSector = 48 := by simp [SourceSector]
theorem all_labelled_choices_card : Fintype.card (Sector × Sector) = 2304 := by
  rw [Fintype.card_prod,sector_card]

end Holant.Certificates.NormalizedDihedralQ6
