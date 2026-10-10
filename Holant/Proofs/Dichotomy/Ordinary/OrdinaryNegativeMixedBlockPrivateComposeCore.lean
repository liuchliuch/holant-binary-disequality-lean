import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockParityCompose
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockSource

/-! Flatten fixed heterogeneous private resources into an actual outer recipe.
Every literal outer-node occurrence has its own dependent private block.
Fresh variables are the finite sigma type of occurrence and private index;
no dictionary, virtual label, or realization backend is presumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeCore
open Holant
open OrdinaryNegativeMixedBlockData
namespace C
export OrdinaryNegativeMixedBlockCompose (substitute)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {v s n l : ℕ} {b c : ℕ→ℕ}
variable (outer : Recipe (u:=1) (s:=v) (a:=fun _=>n+l) (b:=b))
variable (k : Fin v→ℕ)

abbrev Occurrence := Fin (outer 0).length
def node (i : Occurrence outer) := (outer 0).get i
abbrev Private := (i : Occurrence outer) × Fin (k (node outer i).1)
abbrev freshCount : ℕ := Fintype.card (Private outer k)
def freshEquiv : Private outer k ≃ Fin (freshCount outer k) := Fintype.equivFin _
abbrev privateCount : ℕ := l+freshCount outer k

def oldPort : Fin (n+l)→Fin (n+privateCount outer k) :=
  Fin.addCases (Fin.castAdd (privateCount outer k))
    (fun j=>Fin.natAdd n (Fin.castAdd (freshCount outer k) j))

def oldScope : Bool ⊕ Fin (n+l)→Bool ⊕ Fin (n+privateCount outer k) :=
  Sum.map id (oldPort outer k)

def privatePort (i : Occurrence outer) (j : Fin (k (node outer i).1)) :
    Fin (n+privateCount outer k) :=
  Fin.natAdd n (Fin.natAdd l (freshEquiv outer k ⟨i,j⟩))

def scope (i : Occurrence outer) :
    Fin (b (node outer i).1.val+k (node outer i).1)→Bool ⊕ Fin (n+privateCount outer k) :=
  Fin.addCases (fun j=>oldScope outer k ((node outer i).2 j))
    (fun j=>.inr (privatePort outer k i j))

variable (inner : (j : Fin v)→Recipe (u:=1) (s:=s) (a:=fun _=>b j.val+k j) (b:=c))

def OddPrivate : Prop := ∀j,
  (∀q,Even ((ports (inner j) 0).count (.inl q))) ∧
  (∀i,Odd ((ports (inner j) 0).count (.inr (Fin.castAdd (k j) i)))) ∧
  (∀t,Even ((ports (inner j) 0).count (.inr (Fin.natAdd (b j.val) t))))

def plug (i : Occurrence outer)
    (q : Node (u:=1) (s:=s) (a:=fun _=>b (node outer i).1.val+k (node outer i).1) (b:=c) 0) :
    Node (u:=1) (s:=s) (a:=fun _=>n+privateCount outer k) (b:=c) 0 :=
  ⟨q.1,fun t=>C.substitute (scope outer k i) (q.2 t)⟩

def recipe : Recipe (u:=1) (s:=s) (a:=fun _=>n+privateCount outer k) (b:=c) := fun _=>
  (List.finRange (outer 0).length).flatMap (fun i=>(inner (node outer i).1 0).map (plug outer k i))

theorem ports_eq (j : Fin 1) : ports (recipe outer k inner) j=
    (List.finRange (outer 0).length).flatMap
      (fun i=>(ports (inner (node outer i).1) 0).map (C.substitute (scope outer k i))) := by
  simp only [ports,recipe,List.flatMap_assoc,List.flatMap_map,List.map_flatMap,
    Function.comp_def,plug,List.map_ofFn]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockPrivateComposeCore
end
