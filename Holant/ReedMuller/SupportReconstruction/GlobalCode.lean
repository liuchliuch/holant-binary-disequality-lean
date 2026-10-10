import Holant.ReedMuller.SupportReconstruction.SliceWeight
import Holant.Dihedral.SupportIntegration.ExactProjection

/-! A single global binary code is constructed from the literal local slice
images. No global linearity, dimension or self-duality is supplied. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph Holant.ReedMuller.FlatNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def LocalSlices (S : Set (BinaryVector n)) : Prop :=
  ∀i j : Fin n,i≠j → ∃r : ℕ,∃p : (Fin r × Bool) ≃ Remaining i j,
    ∀x : BinaryVector n,(x∈S ∧ x i=x j) ↔ x∈sliceCode p

 namespace LocalSlices
 variable {S : Set (BinaryVector n)} (A : LocalSlices S)
 include A

 theorem zero_mem (hn : 6≤n) : (0 : BinaryVector n)∈S := by
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  have hij : i≠j := by intro h; have hh:=congrArg Fin.val h; change 0=1 at hh;omega
  obtain ⟨r,p,hp⟩ := A i j hij
  exact ((hp 0).mpr (sliceCode p).zero_mem).1

 theorem add_mem (hn : 6≤n) (x y : BinaryVector n) (hx : x∈S) (hy : y∈S) : x+y∈S := by
  obtain ⟨i,j,hij,hxy⟩ := Fintype.exists_ne_map_eq_of_card_lt (fun k : Fin n=>(x k,y k)) (by
    simp only [Fintype.card_prod,ZMod.card,Fintype.card_fin]
    omega)
  obtain ⟨r,p,hp⟩ := A i j hij
  have hxc := (hp x).mp ⟨hx,congrArg Prod.fst hxy⟩
  have hyc := (hp y).mp ⟨hy,congrArg Prod.snd hxy⟩
  exact ((hp (x+y)).mpr ((sliceCode p).add_mem hxc hyc)).1

 def globalCode (hn : 6≤n) : BinaryCode n where
  carrier := S
  zero_mem' := A.zero_mem hn
  add_mem' := fun hx hy=>A.add_mem hn _ _ hx hy
  smul_mem' := by
    intro c x hx
    rcases (by decide : ∀c : ZMod 2,c=0 ∨ c=1) c with rfl | rfl
    · simpa using A.zero_mem hn
    · simpa using hx

 @[simp] theorem mem_globalCode (hn : 6≤n) (x : BinaryVector n) : x∈A.globalCode hn ↔ x∈S := Iff.rfl

 theorem matchingProjections (hn : 6≤n) :
    Holant.Dihedral.SupportIntegration.MatchingProjections (A.globalCode hn) := by
  intro i j hij
  obtain ⟨r,p,hp⟩ := A i j hij
  refine ⟨r,p,?_⟩
  intro x hx he
  exact sliceCode_matching p x ((hp x).mp ⟨hx,he⟩)

 theorem selfOrthogonal (hn : 6≤n) :
    ∀x : BinaryVector n,x∈A.globalCode hn → ∀y : BinaryVector n,y∈A.globalCode hn → dot x y=0 :=
  Holant.Dihedral.SupportIntegration.selfOrthogonal_of_matchingProjections (A.globalCode hn)
    (by omega) (A.matchingProjections hn)

 theorem weight_dvd_four (hn : 6≤n) (x : BinaryVector n) (hx : x∈S) : 4∣binaryWeight x := by
  obtain ⟨i,j,hij,hxij⟩ := Fintype.exists_ne_map_eq_of_card_lt x (by
    simp only [ZMod.card,Fintype.card_fin]
    omega)
  obtain ⟨r,p,hp⟩ := A i j hij
  exact sliceCode_weight_dvd_four p hij x ((hp x).mp ⟨hx,hxij⟩)

 theorem exactMatchingProjections (hn : 6≤n) :
    Holant.Dihedral.SupportIntegration.ExactMatchingProjections (A.globalCode hn) := by
  intro i j hij
  obtain ⟨r,p,hp⟩ := A i j hij
  refine ⟨r,p,?_⟩
  intro y
  constructor
  · rintro ⟨x,hx,he,hy⟩ e
    have hh := sliceCode_matching p x ((hp x).mp ⟨hx,he⟩) e
    rwa [hy,hy] at hh
  · intro hy
    let t : BinaryVector r := fun e=>y (p (e,false))
    let x := sliceWord p t
    have hmem : x∈sliceCode p := ⟨t,rfl⟩
    have hx := (hp x).mpr hmem
    refine ⟨x,hx.1,hx.2,?_⟩
    intro k
    obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective k
    change sliceWord p t (p (e,b)).val=y (p (e,b))
    rw [sliceWord_port]
    cases b
    · rfl
    · exact hy e

 end LocalSlices
end Holant.ReedMuller.SupportReconstruction
