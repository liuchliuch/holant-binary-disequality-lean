import Holant.ReedMuller.WeightTwoIntegration.Ports
import Holant.ReedMuller.WeightTwoIntegration.CrossSupport

/-! The original perfect matching supplies a literal logical coefficient
table. Full logical support is proved from an actual cross card's unique lift. -/
noncomputable section
namespace Holant.ReedMuller.WeightTwoIntegration
open Holant Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.MatchingConsistency
attribute [local instance] Classical.propDecidable
variable {K : Type*} [Field K] {n : ℕ}

 structure OriginalPairing (f : Signature K n) where
  matching : Pairing (Fin n)
  edge_iff : ∀u v,matching.mate u=v ↔ (weightGraph f).Adj u v

 def originalPairing (htwo : (2:K)≠0) (f : Signature K n) (H : Consistent f) (hd : EqualityDeck f)
    (hn : 6≤n) (u v : Fin n) (huv : (weightGraph f).Adj u v) : OriginalPairing f := by
  let hp := weight_graph_perfect htwo H hd (by simpa using hn) u v huv
  exact ⟨graphPairing (weightGraph f) H.weight_matching hp,graphPairing_mate _ _ _⟩

 namespace OriginalPairing
 variable {f : Signature K n} (C : OriginalPairing f)

 def count : ℕ := edgeCount C.matching
 def ports : (Fin C.count × Bool) ≃ Fin n := originalPorts C.matching
 def logical : Signature K C.count := fun t => f (pairedWord C.ports t)

 theorem arity : 2*C.count=n := twice_edgeCount C.matching
 theorem count_ge_three (hn : 6≤n) : 3≤C.count := by have h:=C.arity; omega

 theorem port_edge (e : Fin C.count) : (weightGraph f).Adj (C.ports (e,false)) (C.ports (e,true)) :=
   (C.edge_iff _ _).mp (originalPorts_mate C.matching e false)

 theorem support_edges (x : Fin n → Bool) (hx : C.matching.Support x) :
     ∀u v,(weightGraph f).Adj u v → x u=x v := by
   intro u v h
   have he := (C.edge_iff u v).mpr h
   have hh := hx u
   rw [he] at hh
   exact hh.symm

 theorem supported_word (H : Consistent f) (x : Fin n → Bool) (hx : f x≠0) : C.matching.Support x := by
   intro u
   have he := (C.edge_iff u (C.matching.mate u)).mp rfl
   exact (H.global_equality u _ he x hx).symm

 theorem full_support (htwo : (2:K)≠0) (H : Consistent f) (hd : EqualityDeck f)
     (hn : 6≤n) (x : Fin n → Bool) (hx : C.matching.Support x) : f x≠0 := by
   obtain ⟨e,d,hed,hbits⟩ := Fintype.exists_ne_map_eq_of_card_lt
     (fun e : Fin C.count => x (C.ports (e,false))) (by
       simp only [Fintype.card_bool,Fintype.card_fin]
       have hh:=C.count_ge_three hn
       omega)
   apply cross_support_nonzero htwo H hd
     (C.ports (e,false)) (C.ports (e,true)) (C.ports (d,false)) (C.ports (d,true))
     (C.port_edge e) (C.port_edge d)
   · intro he
     exact hed (congrArg Prod.fst (C.ports.injective he))
   · intro he
     exact hed (congrArg Prod.fst (C.ports.injective he))
   · exact C.support_edges x hx
   · exact hbits

 theorem logical_nonzero (htwo : (2:K)≠0) (H : Consistent f) (hd : EqualityDeck f)
     (hn : 6≤n) (t : Fin C.count → Bool) : C.logical t≠0 :=
   C.full_support htwo H hd hn _ (pairing_support_pairedWord C.matching t)

 theorem tensor_exact (H : Consistent f) (x : Fin n → Bool) :
     f x=if C.matching.Support x then C.logical (fun e => x (C.ports (e,false))) else 0 := by
   classical
   by_cases hx : C.matching.Support x
   · rw [if_pos hx]
     change f x=f (pairedWord (originalPorts C.matching) (fun e => x (originalPorts C.matching (e,false))))
     rw [pairedWord_reconstruct C.matching x hx]
   · rw [if_neg hx]
     by_contra hh
     exact hx (C.supported_word H x hh)

 end OriginalPairing
end Holant.ReedMuller.WeightTwoIntegration
