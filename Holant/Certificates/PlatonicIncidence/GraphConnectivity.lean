import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Finite
import Lean.Elab.Tactic.Omega

/-! A degree certificate proves connectivity after every small deletion.
Indeed the stated Platonic degrees imply the stronger diameter-two property. -/
namespace Holant.Certificates.PlatonicIncidence
open Finset
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem common_neighbor_outside (G : SimpleGraph V) [DecidableRel G.Adj]
    (d s : ℕ) (hdegree : ∀v,d≤(G.neighborFinset v).card)
    (hlarge : Fintype.card V+s<2*d) (D : Finset V) (hD : D.card≤s) (u v : V) :
    ∃w : V,w∉D ∧ G.Adj u w ∧ G.Adj v w := by
  have hu := hdegree u
  have hv := hdegree v
  have hsum := card_inter_add_card_union (G.neighborFinset u) (G.neighborFinset v)
  have hcard : ((G.neighborFinset u)∪(G.neighborFinset v)).card≤Fintype.card V :=
    card_le_univ _
  have hlt : D.card<((G.neighborFinset u)∩(G.neighborFinset v)).card := by omega
  obtain ⟨w,hw⟩ := sdiff_nonempty_of_card_lt_card hlt
  have hh := mem_sdiff.mp hw
  have hn := mem_inter.mp hh.1
  exact ⟨w,hh.2,by simpa using hn.1,by simpa using hn.2⟩

theorem connected_after_deletion (G : SimpleGraph V) [DecidableRel G.Adj]
    (d s : ℕ) (hdegree : ∀v,d≤(G.neighborFinset v).card)
    (hlarge : Fintype.card V+s<2*d) (hsize : s<Fintype.card V)
    (D : Finset V) (hD : D.card≤s) : (G.induce {v | v∉D}).Connected := by
  have hne : Nonempty {v : V // v∉D} := by
    have hlt : D.card<(Finset.univ : Finset V).card := by simpa using hD.trans_lt hsize
    obtain ⟨v,hv⟩ := sdiff_nonempty_of_card_lt_card hlt
    exact ⟨v,(mem_sdiff.mp hv).2⟩
  letI : Nonempty ({v : V | v∉D} : Set V) := hne
  refine ⟨?_⟩
  intro u v
  obtain ⟨w,hw,hu,hv⟩ := common_neighbor_outside G d s hdegree hlarge D hD u.val v.val
  let z : {v : V // v∉D} := ⟨w,hw⟩
  have huz : (G.induce {v | v∉D}).Adj u z := hu
  have hvz : (G.induce {v | v∉D}).Adj v z := hv
  exact huz.reachable.trans hvz.reachable.symm

end Holant.Certificates.PlatonicIncidence
