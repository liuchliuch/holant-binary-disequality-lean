import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2SparseInteger

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
noncomputable section
open Holant.Pauli.ExoticKlein.SixPort
open GlobalCloseCompletionC2SparseInteger
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000
set_option Elab.async false

def cardRows : Fin 12→Bool→Row := ![(fun t=>if t then [(4,(1)),(7,(1))] else [(0,(1)),(3,(1))]),(fun t=>if t then [(5,(1)),(6,(1))] else [(1,(1)),(2,(1))]),(fun t=>if t then [(2,(1)),(7,(1))] else [(0,(1)),(5,(1))]),(fun t=>if t then [(3,(1)),(6,(1))] else [(1,(1)),(4,(1))]),(fun t=>if t then [(2,(1)),(4,(1))] else [(0,(1)),(6,(1))]),(fun t=>if t then [(3,(1)),(5,(1))] else [(1,(1)),(7,(1))]),(fun t=>if t then [(1,(1)),(7,(1))] else [(0,(1)),(6,(1))]),(fun t=>if t then [(3,(1)),(5,(1))] else [(2,(1)),(4,(1))]),(fun t=>if t then [(1,(1)),(4,(1))] else [(0,(1)),(5,(1))]),(fun t=>if t then [(3,(1)),(6,(1))] else [(2,(1)),(7,(1))]),(fun t=>if t then [(1,(1)),(2,(1))] else [(0,(1)),(3,(1))]),(fun t=>if t then [(5,(1)),(6,(1))] else [(4,(1)),(7,(1))])]
def targetRows : Fin 8→List Row := ![[[(1,(1))],[(2,(1))],[(4,(1))],[(7,(1))]],[[(0,(1))],[(3,(1))],[(5,(1))],[(6,(1))]],[[(0,(1)),(6,(-1))],[(1,(1)),(7,(1))],[(2,(1)),(4,(1))],[(3,(1)),(6,(1))],[(5,(1)),(6,(1))]],[[(0,(1)),(6,(1))],[(1,(1)),(7,(-1))],[(2,(1)),(7,(1))],[(3,(1)),(5,(1))],[(4,(1)),(7,(1))]],[[(0,(1)),(6,(1))],[(1,(1)),(4,(1))],[(2,(1)),(7,(1))],[(3,(1)),(6,(-1))],[(5,(1)),(6,(1))]],[[(0,(1)),(6,(1))],[(1,(1)),(2,(1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(1))],[(5,(1)),(6,(-1))]],[[(0,(1)),(5,(1))],[(1,(1)),(7,(1))],[(2,(1)),(7,(-1))],[(3,(1)),(6,(1))],[(4,(1)),(7,(1))]],[[(0,(1)),(3,(1))],[(1,(1)),(7,(1))],[(2,(1)),(7,(1))],[(4,(1)),(7,(-1))],[(5,(1)),(6,(1))]]]
def Holds (r : List Row) (x : Fin 8→ℂ) : Prop := LinearCertificate.Satisfies (IntegerCertificate.mapRows (toIRows r)) x
def Safe (x : Fin 8→ℂ) : Prop := ∀c : Fin 12,∃t : Bool,Holds [cardRows c t] x
def Accepted (x : Fin 8→ℂ) : Prop := ∃j : Fin 8,Holds (targetRows j) x
def Covers (r : List Row) : Prop := ∀x,Holds r x→Safe x→Accepted x

theorem covers_accept (r : List Row) (j : Fin 8) (d : Reduction) (literal : d.rows=targetRows j)
    (checked : d.check r=true) : Covers r := by
  intro x h _
  exact ⟨j,literal ▸ d.sound r checked h⟩

theorem covers_split (r : List Row) (c : Fin 12) (d : Bool→Reduction)
    (checked : ∀t,(d t).check (r++[cardRows c t])=true)
    (children : ∀t,Covers (d t).rows) : Covers r := by
  intro x h safe
  obtain ⟨t,ht⟩ := safe c
  apply children t x _ safe
  apply (d t).sound _ (checked t)
  unfold Holds at h ht
  unfold toIRows at h ht ⊢
  simp only [List.map_append,IntegerCertificate.mapRows,List.map_append] at h ht ⊢
  exact (LinearCertificate.satisfies_append _ _ _).mpr ⟨h,ht⟩

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4Union
