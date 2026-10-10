import Holant.Certificates.MatchingContractionClosure.SinglePair
import Mathlib.Logic.Equiv.Prod
import Mathlib.Data.Fintype.Pi

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
variable {P Q E : Type*} [DecidableEq E]

/-- The bijection specifies every surviving port and every ordered closure
endpoint exactly once, so disjointness is intrinsic. -/
abbrev CollectionPorts (P Q E : Type*) := (Q ⊕ (E × Bool)) ≃ P

theorem collection_pair_distinct (p : CollectionPorts P Q E) (e : E) :
    p (.inr (e,false)) ≠ p (.inr (e,true)) := by
  intro he
  have h := congrArg Prod.snd (Sum.inr.inj (p.injective he))
  cases h

def collectionTailMap (p : CollectionPorts P Q E) (e : E) :
    (Q ⊕ (OtherEdges e × Bool)) → Remaining (p (.inr (e,false))) (p (.inr (e,true)))
  | .inl q => ⟨p (.inl q),by
      constructor <;> intro h <;> cases p.injective h⟩
  | .inr (d,b) => ⟨p (.inr (d.val,b)),by
      constructor <;> intro h <;> exact d.property (congrArg Prod.fst (Sum.inr.inj (p.injective h)))⟩

theorem collectionTailMap_injective (p : CollectionPorts P Q E) (e : E) :
    Function.Injective (collectionTailMap p e) := by
  intro s t h
  rcases s with q | ⟨d,b⟩ <;> rcases t with q' | ⟨d',b'⟩
  · have hh := p.injective (congrArg Subtype.val h)
    exact congrArg Sum.inl (Sum.inl.inj hh)
  · have hh := p.injective (congrArg Subtype.val h)
    cases hh
  · have hh := p.injective (congrArg Subtype.val h)
    cases hh
  · have hh := p.injective (congrArg Subtype.val h)
    have hpair : (d.val,b)=(d'.val,b') := Sum.inr.inj hh
    apply congrArg Sum.inr
    apply Prod.ext
    · exact Subtype.ext (congrArg Prod.fst hpair)
    · exact congrArg (fun q : E × Bool => q.2) hpair

theorem collectionTailMap_surjective (p : CollectionPorts P Q E) (e : E) :
    Function.Surjective (collectionTailMap p e) := by
  intro x
  obtain ⟨s,hs⟩ := p.surjective x.val
  rcases s with q | ⟨d,b⟩
  · exact ⟨.inl q,Subtype.ext hs⟩
  · have hd : d≠e := by
      intro hd
      subst d
      cases b
      · exact x.property.1 hs.symm
      · exact x.property.2 hs.symm
    exact ⟨.inr (⟨d,hd⟩,b),Subtype.ext hs⟩

def collectionTailPorts (p : CollectionPorts P Q E) (e : E) :
    CollectionPorts (Remaining (p (.inr (e,false))) (p (.inr (e,true)))) Q (OtherEdges e) :=
  Equiv.ofBijective (collectionTailMap p e)
    ⟨collectionTailMap_injective p e,collectionTailMap_surjective p e⟩

@[simp] theorem collectionTailPorts_boundary (p : CollectionPorts P Q E) (e : E) (q : Q) :
    (collectionTailPorts p e (.inl q)).val=p (.inl q) := rfl

@[simp] theorem collectionTailPorts_edge (p : CollectionPorts P Q E) (e : E)
    (d : OtherEdges e) (b : Bool) :
    (collectionTailPorts p e (.inr (d,b))).val=p (.inr (d.val,b)) := rfl

def collectionAssignment (p : CollectionPorts P Q E) (x : Q → Bool) (y : E → Bool × Bool) : P → Bool :=
  fun i => match p.symm i with
    | .inl q => x q
    | .inr (e,b) => if b then (y e).2 else (y e).1

@[simp] theorem collectionAssignment_boundary (p : CollectionPorts P Q E) (x : Q → Bool)
    (y : E → Bool × Bool) (q : Q) : collectionAssignment p x y (p (.inl q))=x q := by
  simp [collectionAssignment]

@[simp] theorem collectionAssignment_edge (p : CollectionPorts P Q E) (x : Q → Bool)
    (y : E → Bool × Bool) (e : E) (b : Bool) :
    collectionAssignment p x y (p (.inr (e,b)))=if b then (y e).2 else (y e).1 := by
  simp [collectionAssignment]

end
end Holant.Certificates.MatchingContractionClosure
