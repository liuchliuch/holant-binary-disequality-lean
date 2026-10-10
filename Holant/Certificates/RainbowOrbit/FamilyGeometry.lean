import Holant.Certificates.RainbowOrbit.PortPermutations

namespace Holant.Certificates.RainbowOrbit
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def FamilyInMatching (G : BinaryMatrix→Prop) (r : Fin 3) (F : FourTensor) : Prop :=
  ∃ U V : BinaryMatrix,G U ∧ G V ∧ F=matchingTensor r U V

def FamilyRainbow (G : BinaryMatrix→Prop) (p : Fin 3→Point) : Prop :=
  (∀r,∃F,∃hF : F≠0,FamilyInMatching G r F ∧ p r=Projectivization.mk ℂ F hF) ∧
    Projectivization.IsCollinear {p 0,p 1,p 2}

def FamilyRainbowLine (G : BinaryMatrix→Prop) (S : Finset Point) : Prop :=
  ∃p : Fin 3→Point,FamilyRainbow G p ∧ S=points p

theorem range_three (p : Fin 3→Point) : Set.range p={p 0,p 1,p 2} := by
  ext x
  simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff]
  constructor
  · rintro ⟨r,rfl⟩
    fin_cases r <;> simp
  · rintro (rfl|rfl|rfl)
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩

theorem range_permute (p : Fin 3→Point) (e : Equiv.Perm (Fin 3)) :
    Set.range (fun r => p (e r))=Set.range p := by
  ext x
  constructor
  · rintro ⟨r,rfl⟩
    exact ⟨e r,rfl⟩
  · rintro ⟨r,rfl⟩
    exact ⟨e.symm r,by change p (e (e.symm r))=p r; rw [e.apply_symm_apply]⟩

theorem FamilyRainbow.map_act {G : BinaryMatrix→Prop}
    (htranspose : ∀{U : BinaryMatrix},G U→G U.transpose)
    (hmul : ∀{U V : BinaryMatrix},G U→G V→G (U*V))
    {p : Fin 3→Point} (hp : FamilyRainbow G p) (L : Legs)
    (hL : ∀j,G (L j)) (hd : ∀j,(L j).det≠0) :
    FamilyRainbow G (fun r => pointAction L hd (p r)) := by
  constructor
  · intro r
    obtain ⟨F,hF,⟨U,V,hU,hV,rfl⟩,he⟩ := hp.1 r
    refine ⟨act L (matchingTensor r U V),act_nonzero L hd hF,?_,?_⟩
    · have hm (i j : Fin 4) (M : BinaryMatrix) (hM : G M) : G (L i*M*(L j).transpose) :=
        hmul (hmul (hL i) hM) (htranspose (hL j))
      fin_cases r
      · exact ⟨_,_,hm 0 1 U hU,hm 2 3 V hV,act_P0 L U V⟩
      · exact ⟨_,_,hm 0 2 U hU,hm 1 3 V hV,act_P1 L U V⟩
      · exact ⟨_,_,hm 0 3 U hU,hm 1 2 V hV,act_P2 L U V⟩
    · change pointAction L hd (p r)=_
      rw [he,pointAction_mk]
  · have hh := pointAction_collinear L hd _ hp.2
    simpa only [Set.image_insert_eq,Set.image_singleton] using hh

theorem FamilyRainbow.map_adjacent {G : BinaryMatrix→Prop}
    (htranspose : ∀{U : BinaryMatrix},G U→G U.transpose)
    {p : Fin 3→Point} (hp : FamilyRainbow G p) (j : Fin 3) :
    FamilyRainbow G (fun r => portPoint (adjacent j) (p ((adjacentLabels j).symm r))) := by
  constructor
  · intro r
    obtain ⟨F,hF,⟨U,V,hU,hV,rfl⟩,he⟩ := hp.1 ((adjacentLabels j).symm r)
    have hn : Tensor.reindex (adjacent j) (matchingTensor ((adjacentLabels j).symm r) U V)≠0 := by
      intro hz
      apply hF
      apply portLinear_injective (adjacent j)
      exact hz
    obtain ⟨S,T,hS,hT,ht⟩ := adjacent_matching G htranspose j ((adjacentLabels j).symm r) U V hU hV
    refine ⟨_,hn,⟨S,T,hS,hT,?_⟩,?_⟩
    · simpa only [Equiv.apply_symm_apply] using ht
    · change portPoint (adjacent j) (p ((adjacentLabels j).symm r))=_
      rw [he]
      rfl
  · have hh := portPoint_collinear (adjacent j) (Set.range p) (by simpa only [range_three] using hp.2)
    rw [←range_three (fun r => portPoint (adjacent j) (p ((adjacentLabels j).symm r)))]
    have he : Set.range (fun r => portPoint (adjacent j) (p ((adjacentLabels j).symm r)))=
        portPoint (adjacent j) '' Set.range p := by
      rw [←range_permute p (adjacentLabels j).symm]
      exact Set.range_comp (portPoint (adjacent j)) (fun r => p ((adjacentLabels j).symm r))
    rw [he]
    exact hh

end
end Holant.Certificates.RainbowOrbit
