import Holant.Matching.StableQuaternaryBoundary.RepresentativeLines

/-! The full one-copy matching-deck condition in the literal original
coordinates. The certificate hypotheses are proved by selecting its undressed
cards, retaining all closing labels, all six pairs, and both port orientations. -/
noncomputable section
namespace Holant.Matching.StableQuaternaryBoundary
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
set_option backward.isDefEq.respectTransparency false

abbrev Dressing (row : SourceRow) := Fin 4 → Option (Label row × Bool)

def dressAt {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (q : Signature Scalar 4)
    (δ : Dressing row) (i : Fin 4) : Signature Scalar 4 :=
  match δ i with
  | none => q
  | some (k,reverse) =>
      Holant.Projective.CyclicDressing.onePort q i (orient reverse (matrix row reps k))

/-- Each selected original port receives its fixed representative through
one native X edge; no common basis change or scalar division occurs. -/
def dress {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (q : Signature Scalar 4)
    (δ : Dressing row) : Signature Scalar 4 :=
  dressAt row reps (dressAt row reps (dressAt row reps (dressAt row reps q δ 0) δ 1) δ 2) δ 3

@[simp] theorem dress_none {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (q : Signature Scalar 4) :
    dress row reps q (fun _ => none)=q := rfl

/-- Source Definition 5.6 at arity four: all dressed proper cards, with
fixed representative scalars, arbitrary matching labels, both binary
orientations, every ordered deleted pair and every residual order. -/
def MatchingDeck {F : SignatureFamily Scalar} (row : SourceRow)
    (reps : SourceRepresentatives F row) (q : Signature Scalar 4) : Prop :=
  ∀ (δ : Dressing row) (e : Equiv.Perm (Fin 4)) (k : Label row) (reverse : Bool),
    let B := physicalCard (dress row reps q δ) e (orient reverse (matrix row reps k))
    B=0 ∨ OrientedMatching row reps B

theorem undressed_card {F : SignatureFamily Scalar} (row : SourceRow)
    (hrow : row.Valid) (reps : SourceRepresentatives F row) (q : Signature Scalar 4)
    (hd : MatchingDeck row reps q) (e : Equiv.Perm (Fin 4)) (k : Label row) :
    physicalCard q e (matrix row reps k)=0 ∨
      ActualLine row reps (physicalCard q e (matrix row reps k)) := by
  have h := hd (fun _ => none) e k false
  change physicalCard q e (matrix row reps k)=0 ∨
    OrientedMatching row reps (physicalCard q e (matrix row reps k)) at h
  exact h.imp id (orientedMatching_actualLine row hrow reps)

def pairMap (i : Fin 3) (side order : Bool) (j : Fin 4) : Fin 4 :=
  let f : Fin 4 → Fin 4 :=
    if side then
      if i=0 then ![2,3,0,1] else if i=1 then ![2,0,3,1] else ![2,0,1,3]
    else
      if i=0 then ![0,1,2,3] else if i=1 then ![0,2,1,3] else ![0,2,3,1]
  if order then Equiv.swap 2 3 (f j) else f j

theorem pairMap_bijective (i : Fin 3) (side order : Bool) :
    Function.Bijective (pairMap i side order) := by
  fin_cases i <;> cases side <;> cases order <;> decide +kernel

def pairOrder (i : Fin 3) (side order : Bool) : Equiv.Perm (Fin 4) :=
  (Equiv.ofBijective (pairMap i side order) (pairMap_bijective i side order)).symm

theorem pairOrder_word (i : Fin 3) (side order a b u v : Bool) :
    Holant.Marked.SupportAtlas.permuteWord (pairOrder i side order) ![a,b,u,v]=
      Holant.Projective.CyclicQuaternary.join i side a b
        (if order then v else u) (if order then u else v) := by
  funext j
  fin_cases i <;> cases side <;> cases order <;> fin_cases j <;> rfl

/-- The C2 six-pair indexing is the same finite sum at the same physical
ports as the general 24-permutation card indexing, including residual reversal. -/
theorem pairOrder_card (q : Signature Scalar 4) (i : Fin 3) (side order : Bool) (B : Mat) :
    physicalCard q (pairOrder i side order) B=
      Holant.Projective.CyclicQuaternary.Physical.orderedPhysicalCard q i side order B := by
  funext u v
  simp only [physicalCard,contract0,reorder,pairOrder_word]
  cases order <;> rfl

/-- No A.7/A.8 deck hypothesis is supplied separately: each is the exact
undressed subdeck of the complete source matching deck. -/
theorem sourceDeck_of_matchingDeck {F : SignatureFamily Scalar} (row : SourceRow)
    (hrow : row.Valid) (reps : SourceRepresentatives F row) (q : Signature Scalar 4)
    (hd : MatchingDeck row reps q) : SourceDeck row reps q := by
  cases row with
  | c2 =>
    intro i side order p
    have h := undressed_card .c2 hrow reps q hd (pairOrder i side order) p
    change physicalCard q (pairOrder i side order) (reps.matrix p)=0 ∨
      C2.ActualLine reps (physicalCard q (pairOrder i side order) (reps.matrix p)) at h
    rwa [pairOrder_card] at h
  | monomial m =>
    intro e p t
    have h := undressed_card (.monomial m) hrow reps q hd e (p,t)
    rcases h with hz | ⟨⟨p',t'⟩,c,hc,hB⟩
    · exact Or.inl hz
    · exact Or.inr ⟨p',t',c,hc,hB⟩
  | standardKlein => exact fun e k => undressed_card .standardKlein hrow reps q hd e k
  | exoticKlein => exact fun e k => undressed_card .exoticKlein hrow reps q hd e k

end Holant.Matching.StableQuaternaryBoundary
