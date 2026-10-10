import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeMixedBlockConstants

/-! Original-row minors as actual heterogeneous recipe nodes. Arity transport
is explicit and preserves both all literal ports and their exact products. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockLiteral
open Holant
open OrdinaryNegativeMixedBlockData
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseBundle (evaluate)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false

variable {u s n : ℕ} {a b : ℕ→ℕ}

def nodes (i : Fin u) (label : Fin s) (h : b label.val=n)
    (ps : List (Fin n→Bool ⊕ Fin (a i.val))) :
    List (Node (u:=u) (s:=s) (a:=a) (b:=b) i) :=
  ps.map (fun p=>⟨label,fun k=>p (Fin.cast h k)⟩)

theorem nodes_ports (i : Fin u) (label : Fin s) (h : b label.val=n)
    (ps : List (Fin n→Bool ⊕ Fin (a i.val))) :
    (nodes i label h ps).flatMap (fun node=>List.ofFn node.2)=ps.flatMap List.ofFn := by
  subst n
  simp only [nodes,List.flatMap_map,Function.comp_def,Fin.cast_refl,id_eq]

variable {K : Type} [CommSemiring K]

theorem signature_apply {m n : ℕ} (f : Signature K m) (g : Signature K n)
    (h : (⟨m,f⟩ : AnySignature K)=⟨n,g⟩) (x : Fin n→Bool) :
    f (fun i=>x (Fin.cast (congrArg Sigma.fst h) i))=g x := by
  cases h
  rfl

theorem nodes_value (H : (j : Fin s)→Signature K (b j.val)) (i : Fin u)
    (label : Fin s) (f : Signature K n)
    (h : (⟨b label.val,H label⟩ : AnySignature K)=⟨n,f⟩)
    (ps : List (Fin n→Bool ⊕ Fin (a i.val))) (x : Fin (a i.val)→Bool) :
    ((nodes i label (congrArg Sigma.fst h) ps).map
      (fun node=>H node.1 (fun j=>Sum.elim id x (node.2 j)))).prod=B.evaluate f ps x := by
  simp only [nodes,List.map_map,Function.comp_def]
  unfold B.evaluate
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  exact signature_apply (H label) f h (fun j=>Sum.elim id x (p j))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeMixedBlockLiteral
end
