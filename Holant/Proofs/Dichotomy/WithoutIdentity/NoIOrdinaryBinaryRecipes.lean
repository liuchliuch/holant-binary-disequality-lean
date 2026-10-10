import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralEvenOperations
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralUnsignedBinary

/-! Five unsigned actual even-binary candidates and their positive-power
Gram recipes. Every private variable and every original occurrence remains
inside the proved even-recipe compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryBinaryRecipes
open Holant Holant.Tractable
namespace B
export OrdinaryNegativeSparseMixingSource (Block)
end B
namespace O
export NoXGeneralEvenOperations (gadget gadget_value)
end O
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionGadget
  (Gadget denote direct direct_value trace trace_value)
end G
namespace E
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
set_option linter.unusedSimpArgs false

def ports (i j : Fin 3) : Fin 2→Bool⊕Fin 3:=![Sum.inr i,Sum.inr j]
def directPorts (i j : Fin 2) : Fin 2→Bool⊕Fin 2:=![Sum.inr i,Sum.inr j]
def candidateGadget : Fin 5→G.Gadget 2 2 :=
  ![G.direct [directPorts 0 1],G.direct [directPorts 1 0],
    G.direct [directPorts 0 1,directPorts 0 1],
    G.trace (G.direct [ports 0 1,ports 1 2]),G.trace (G.direct [ports 0 1,ports 2 1])]
def gramGadget (k : ℕ) : G.Gadget 2 2:=
  G.trace (G.direct (ports 0 2::List.replicate k (ports 1 2)))

variable {K : Type} [Field K] {s : ℕ} {b : ℕ→ℕ}
def candidate (f : Signature K 2) (i : Fin 5) : Signature K 2 :=
  ![f,(fun x=>f ![x 1,x 0]),(fun x=>f x^2),
    (fun x=>f x*(f ![x 1,false]+f ![x 1,true])),
    (fun x=>f x*(f ![false,x 1]+f ![true,x 1]))] i
def gramPower (f : Signature K 2) (k : ℕ) : Signature K 2:=
  fun x=>∑v : Bool,f ![x 0,v]*f ![x 1,v]^k
def candidateBlock (row : B.Block (s:=s) (b:=b) 2) (i : Fin 5) : B.Block (s:=s) (b:=b) 2 :=
  O.gadget row (candidateGadget i)
def gramBlock (row : B.Block (s:=s) (b:=b) 2) (k : ℕ) : B.Block (s:=s) (b:=b) 2 :=
  O.gadget row (gramGadget k)

theorem sub_ports (z : Fin 3→Bool) (i j : Fin 3) : E.substitute (ports i j) z=![z i,z j] := by
  funext k; fin_cases k <;> rfl
theorem sub_direct (z : Fin 2→Bool) (i j : Fin 2) : E.substitute (directPorts i j) z=![z i,z j] := by
  funext k; fin_cases k <;> rfl
theorem self_word (z : Fin 2→Bool) : ![z 0,z 1]=z := by funext k;fin_cases k <;> rfl

variable (H : (i : Fin s)→Signature K (b i.val)) (row : B.Block (s:=s) (b:=b) 2)

theorem candidate_value (i : Fin 5) (x : Fin 2→Bool) :
    (candidateBlock row i).signature H x=candidate (row.signature H) i x := by
  rw [candidateBlock,O.gadget_value]
  have cases : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 := by omega
  rcases cases with rfl|rfl|rfl|rfl|rfl
  · change G.denote (row.signature H) (G.direct [directPorts 0 1]) x=row.signature H x
    simp only [G.direct_value,E.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,sub_direct,self_word,mul_one]
  · change G.denote (row.signature H) (G.direct [directPorts 1 0]) x=row.signature H ![x 1,x 0]
    simp only [G.direct_value,E.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,sub_direct,mul_one]
  · change G.denote (row.signature H) (G.direct [directPorts 0 1,directPorts 0 1]) x=row.signature H x^2
    simp only [G.direct_value,E.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,sub_direct,self_word,mul_one,pow_two]
  · change G.denote (row.signature H) (G.trace (G.direct [ports 0 1,ports 1 2])) x=
      row.signature H x*(row.signature H ![x 1,false]+row.signature H ![x 1,true])
    simp only [G.trace_value,G.direct_value,E.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,sub_ports,mul_one]
    simp [Fintype.sum_bool,Fin.snoc,mul_add,add_comm,self_word]
  · change G.denote (row.signature H) (G.trace (G.direct [ports 0 1,ports 2 1])) x=
      row.signature H x*(row.signature H ![false,x 1]+row.signature H ![true,x 1])
    simp only [G.trace_value,G.direct_value,E.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,sub_ports,mul_one]
    simp [Fintype.sum_bool,Fin.snoc,mul_add,add_comm,self_word]

theorem gram_value (k : ℕ) (x : Fin 2→Bool) :
    (gramBlock row k).signature H x=gramPower (row.signature H) k x := by
  rw [gramBlock,O.gadget_value,gramGadget,G.trace_value]
  simp only [G.direct_value,E.evaluate,List.map_cons,List.map_replicate,List.prod_cons,List.prod_replicate,
    sub_ports,gramPower]
  apply Finset.sum_congr rfl
  intro v _
  simp [Fin.snoc]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryBinaryRecipes
end
