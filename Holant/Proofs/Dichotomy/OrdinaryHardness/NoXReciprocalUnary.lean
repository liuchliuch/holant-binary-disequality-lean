import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockLiteral

/-! Tie the two ports of an actual diagonal row to obtain an even unary block. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalUnary
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData
namespace L
export OrdinaryNegativeMixedBlockLiteral (nodes nodes_ports nodes_value)
end L
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
namespace T
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionTensor (substitute)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 32768
set_option Elab.async false
variable {K : Type} [Field K] {s n : ℕ} {a : ℕ→ℕ}
variable (target : K)
variable (H : (j : Fin s)→Signature K (a j.val)) (label : Fin s)

def signature : Signature K 2 := fun x=>if x 0=x 1 then (if x 0 then target else 1) else 0

variable (literal : (⟨a label.val,H label⟩ : AnySignature K)=⟨2,signature target⟩)
variable (q : Bool ⊕ Fin n)

def rows : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=a) :=
  fun i=>L.nodes i label (congrArg Sigma.fst literal) [fun _ : Fin 2=>q]

theorem balanced : EvenRecipe (rows target H label literal q) := by
  intro i p
  fin_cases i
  rw [ports,rows,L.nodes_ports]
  change Even (([q,q] : List (Bool ⊕ Fin n)).count p)
  by_cases h : q=p <;> simp [h]

theorem coefficient_value (z : Fin n→Bool) :
    coefficient H (rows target H label literal q) 0 z=if Sum.elim id z q then target else 1 := by
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient rows
  erw [L.nodes_value H 0 label (signature target) literal]
  simp only [B.evaluate,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
  simp [signature,T.substitute]

variable (base : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=a))

def append : Recipe (u:=1) (s:=s) (a:=fun _=>n) (b:=a) := fun i=>base i++rows target H label literal q i

theorem append_balanced (hbase : EvenRecipe base) : EvenRecipe (append target H label literal q base) := by
  intro i p
  have hsign:=balanced target H label literal q i p
  change Even (((base i++rows target H label literal q i).flatMap (fun node=>List.ofFn node.2)).count p)
  rw [List.flatMap_append,List.count_append]
  exact (hbase i p).add hsign

theorem append_value (z : Fin n→Bool) :
    coefficient H (append target H label literal q base) 0 z=
      coefficient H base 0 z*(if Sum.elim id z q then target else 1) := by
  rw [←coefficient_value target H label literal q z]
  unfold coefficient Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyBundleValue.coefficient append
  rw [List.map_append,List.prod_append]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalUnary
end
