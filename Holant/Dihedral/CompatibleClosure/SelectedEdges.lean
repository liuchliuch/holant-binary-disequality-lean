import Holant.Dihedral.CompatibleClosure.ProductExtraction
import Holant.Dihedral.EndpointParallelogram.Factors

/-! A genuinely different matching edge selects two distinct original factors.
Their local orientation is computed from the original port bijection. -/
namespace Holant.Dihedral.CompatibleClosure
open Holant Holant.Marked Holant.Dihedral.EndpointParallelogram

variable {n r : ℕ}

/-- Different partner incidence is exactly what makes the two selected factor
indices distinct. No decomposition or edge-selection certificate is supplied. -/
theorem different_edge_indices (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n)
    (huv : u ≠ v) (hd : (Pairing.ofPorts p).mate u ≠ v) :
    (p.symm u).1 ≠ (p.symm v).1 := by
  intro he
  apply hd
  have hb : (p.symm u).2 ≠ (p.symm v).2 := by
    intro hh
    apply huv
    apply p.symm.injective
    exact Prod.ext he hh
  have hv : (!(p.symm u).2) = (p.symm v).2 := by
    cases hu : (p.symm u).2 <;> cases hv : (p.symm v).2 <;> simp_all
  change p ((p.symm u).1,!(p.symm u).2) = v
  rw [he,hv]
  exact p.apply_symm_apply v

def selectMask (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n) (e : Fin r) : Bool :=
  if e = (p.symm u).1 then !(p.symm u).2
  else if e = (p.symm v).1 then (p.symm v).2 else false

def selectedPorts (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n) : (Fin r × Bool) ≃ Fin n :=
  (flipSlots (selectMask p u v)).trans p

/-- The first selected factor points toward u, and the second points away
from v, exactly as required by the literal fusion formula. -/
theorem selected_endpoints (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n)
    (huv : u ≠ v) (hd : (Pairing.ofPorts p).mate u ≠ v) :
    selectedPorts p u v ((p.symm u).1,true) = u ∧
    selectedPorts p u v ((p.symm v).1,false) = v := by
  have he := different_edge_indices p u v huv hd
  constructor
  · change p ((p.symm u).1,true ^^ selectMask p u v (p.symm u).1) = u
    simp only [selectMask,ite_true,Bool.true_xor,Bool.not_not]
    exact p.apply_symm_apply u
  · change p ((p.symm v).1,false ^^ selectMask p u v (p.symm v).1) = v
    simp only [selectMask,Ne.symm he,ite_false,ite_true,Bool.false_xor]
    exact p.apply_symm_apply v

/-- The opposite endpoints are the actual original partners, not renamed or
chosen substitutes. -/
theorem selected_neighbors (p : (Fin r × Bool) ≃ Fin n) (u v : Fin n)
    (huv : u ≠ v) (hd : (Pairing.ofPorts p).mate u ≠ v) :
    selectedPorts p u v ((p.symm u).1,false) = (Pairing.ofPorts p).mate u ∧
    selectedPorts p u v ((p.symm v).1,true) = (Pairing.ofPorts p).mate v := by
  have he := different_edge_indices p u v huv hd
  constructor
  · simp [selectedPorts,flipSlots,selectMask,Pairing.ofPorts]
  · simp [selectedPorts,flipSlots,selectMask,Pairing.ofPorts,Ne.symm he]

end Holant.Dihedral.CompatibleClosure
