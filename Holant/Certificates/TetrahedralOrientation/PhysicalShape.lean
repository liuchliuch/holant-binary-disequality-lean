import Holant.Certificates.TetrahedralOrientation.Data
import Holant.Certificates.FourthRootOdd.NetworkTools
import Holant.NativeNetwork
import Holant.NetworkAsGadget

/-! One genuine six-port ancestor, an actual I binary closing original ports1/3,
and four actual dressing binaries. All six connecting edges are native X. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def binarySignature (U : Binary) : Signature ℂ 2 := fun x => U (x 0) (x 1)
def nativeLeg (L : Binary) : Binary := Kernel.mul L Signature.disequality

def terminalArity : Fin 6 → ℕ := Fin.cases 6 (fun _ => 2)

def terminalPortMap : (Σ v : Fin 6, Fin (terminalArity v)) → (Fin 4 ⊕ (Fin 6 × Bool)) := fun p =>
  Fin.cases (fun i => .inr (contractOrder i,false))
    (fun v => Fin.cases (fun i : Fin 2 => .inr ((if i = 0 then 0 else 1),true))
      (fun j => fun i : Fin 2 => if i = 0 then .inl j else .inr (j.succ.succ,true)) v) p.1 p.2

def terminalPortInv : (Fin 4 ⊕ (Fin 6 × Bool)) → (Σ v : Fin 6, Fin (terminalArity v))
  | .inl j => ⟨j.succ.succ,(0 : Fin 2)⟩
  | .inr (e,b) => if b then
      Fin.cases ⟨(1 : Fin 6),(0 : Fin 2)⟩
        (fun e' => Fin.cases ⟨(1 : Fin 6),(1 : Fin 2)⟩
          (fun j => ⟨j.succ.succ,(1 : Fin 2)⟩) e') e
    else ⟨(0 : Fin 6),contractOrder e⟩

def terminalShape : NetworkShape 4 where
  vertices := 6
  arity := terminalArity
  edges := 6
  ports := {
    toFun := terminalPortMap
    invFun := terminalPortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [terminalArity] at i <;> fin_cases i <;> rfl
    right_inv q := by
      cases q with
      | inl j => fin_cases j <;> rfl
      | inr q => rcases q with ⟨e,b⟩; fin_cases e <;> cases b <;> rfl }

def terminalLabels (s : Orientation) : (v : Fin 6) → Signature ℂ (terminalArity v) :=
  Fin.cases (ancestor s) (fun v => Fin.cases (binarySignature Q0)
    (fun j => binarySignature (nativeLeg (legs s j))) v)

def terminalNetwork (s : Orientation) : Network ℂ 4 where
  shape := terminalShape
  vertex := terminalLabels s
  edge := fun _ => Signature.disequality

/-- The contraction alone is already an actual I-edge graph, with the original ancestor label. -/
def cardNetwork (s : Orientation) : Network ℂ 4 :=
  (FourthRootOdd.reorderNetwork (FourthRootOdd.singleVertexNetwork (ancestor s)) contractOrder).contract Q0

theorem cardNetwork_denote (s : Orientation) : (cardNetwork s).denote = card s := by
  rw [cardNetwork,Network.denote_contract,FourthRootOdd.reorderNetwork_denote,
    FourthRootOdd.singleVertexNetwork_denote]
  rfl

theorem card_realizes (s : Orientation) :
    Gadget.Realizes ({⟨6,ancestor s⟩} : SignatureFamily ℂ) .equality (card s) := by
  have h := Gadget.realizes_network (cardNetwork s) ({⟨6,ancestor s⟩} : SignatureFamily ℂ) .equality
    (by intro v; exact Set.mem_singleton _)
    (by intro e; change Fin 1 at e; have he : e = 0 := Subsingleton.elim _ _; subst e; rfl)
  rwa [cardNetwork_denote] at h

end
end Holant.Certificates.TetrahedralOrientation
