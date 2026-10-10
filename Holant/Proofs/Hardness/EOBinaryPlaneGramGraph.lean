import Holant.Proofs.Hardness.EOBinaryPlaneOpen
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Four explicit opposite-pair lift vertices produce the Gram-type binary
sum. The two supplied labels are lift f and lift g; g is arbitrary, and no
conjugate signature is declared available. Four original vertices, six native
X edges, and four ordered boundary ports are retained in the literal template. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramGraph
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace C
export EOBinaryPlaneCore (lift)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

abbrev Ends := Fin 4 ⊕ (Fin 6 × Bool)
def routes : Fin 4 → Fin 4 → Ends := ![
  ![.inl 0,.inr (0,false),.inr (3,true),.inr (2,false)],
  ![.inl 2,.inr (1,false),.inr (2,true),.inr (3,false)],
  ![.inr (0,true),.inl 1,.inr (5,true),.inr (4,false)],
  ![.inr (1,true),.inl 3,.inr (4,true),.inr (5,false)]]

def owners : Ends → (Σ_ : Fin 4,Fin 4)
  | .inl j => ![⟨0,0⟩,⟨2,1⟩,⟨1,0⟩,⟨3,1⟩] j
  | .inr (e,b) => if b then ![⟨2,0⟩,⟨3,0⟩,⟨1,2⟩,⟨0,2⟩,⟨3,2⟩,⟨2,2⟩] e
    else ![⟨0,1⟩,⟨1,1⟩,⟨0,3⟩,⟨1,3⟩,⟨2,3⟩,⟨3,3⟩] e

def shape : NetworkShape 4 where
  vertices := 4
  arity _ := 4
  edges := 6
  ports := {
    toFun p := routes p.1 p.2
    invFun := owners
    left_inv := by decide
    right_inv := by decide }

def label : Fin 4→Fin 2 := ![0,1,1,0]

def row (x : Fin 4→Bool) (z : (Fin 6×Bool)→Bool) (v : Fin 4) : Fin 4→Bool :=
  fun j=>Sum.elim x z (routes v j)

def palette {K : Type*} [Zero K] (f g : Signature K 2) (i : Fin 2) : Signature K 4 :=
  if i=0 then C.lift f else C.lift g

def network {K : Type*} [Semiring K] (f g : Signature K 2) : Network K 4 where
  shape := shape
  vertex v := palette f g (label v)
  edge _ := Signature.disequality

def labelling : Labelling shape 2 1 (fun _=>4) where
  vertex := label
  vertex_arity _ := rfl
  edge _ := 0

abbrev template := labelling.template
abbrev valid := labelling.wellFormed

def output {K : Type*} [CommSemiring K] (f g : Signature K 2) : Signature K 2 := fun x=>
  ∑z : Bool,∑w : Bool,f ![x 0,z]*g ![x 1,z]*g ![x 0,w]*f ![x 1,w]

variable {K : Type*} [CommSemiring K] (f g : Signature K 2)

theorem native_sum (x : Fin 4→Bool) : (network f g).denote x=
    ∑a : Fin 6→Bool,
      C.lift f ![x 0,a 0,!(a 3),a 2]*
      C.lift g ![x 2,a 1,!(a 2),a 3]*
      C.lift g ![!(a 0),x 1,!(a 5),a 4]*
      C.lift f ![!(a 1),x 3,!(a 4),a 5] := by
  rw [EOBinaryPlaneOpen.native_sum (network f g) (fun _=>rfl)]
  apply Finset.sum_congr rfl
  intro a _
  change (∏v : Fin 4,palette f g (label v)
    (row x (fun e=>if e.2 then !(a e.1) else a e.1) v))=_
  rw [Fin.prod_univ_four]
  rfl

private theorem sum_cons {m : ℕ} (F : (Fin (m+1)→Bool)→K) :
    (∑x,F x)=∑b : Bool,∑x : Fin m→Bool,F (Fin.cons b x) := by
  classical
  let : Fintype (Bool×(Fin m→Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Bool)).sum_comp,Fintype.sum_prod_type]
  rfl

private theorem sum_nil (F : (Fin 0→Bool)→K) : (∑x,F x)=F Fin.elim0 := by
  have h (x : Fin 0→Bool) : x=Fin.elim0 := by funext i; exact Fin.elim0 i
  simp [h]

private theorem sum_six_bits (W : (Fin 6→Bool)→K) :
    (∑x,W x)=∑a : Bool,∑b : Bool,∑c : Bool,∑d : Bool,∑e : Bool,∑h : Bool,
      W ![a,b,c,d,e,h] := by
  simp only [sum_cons,sum_nil]
  repeat' (apply Finset.sum_congr rfl; intro z _)
  congr 1

/-- The full graph identity is proved from its sixteen incidence entries and
native edge sum. No local denotation equation is a caller premise. -/
theorem denote : (network f g).denote=C.lift (output f g) := by
  funext x
  rw [native_sum,sum_six_bits]
  simp only [Fintype.sum_bool]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [C.lift,output,h0,h1,h2,h3] <;> ring

theorem template_denote :
    (template.network valid (palette f g) (fun _ : Fin 1=>Signature.disequality)).denote=
      C.lift (output f g) := by
  have h := Labelling.denote_template_of_labels labelling (palette f g)
    (fun _ : Fin 1=>Signature.disequality) (network f g).vertex (network f g).edge
    (fun _ _=>rfl) (fun _ _ _=>rfl)
  exact h.trans (denote f g)

/-- The actual label and local-port records, including both ends of each edge. -/
theorem template_rows : template.vertices=[
    (0,[.inl 0,.inr (0,false),.inr (3,true),.inr (2,false)]),
    (1,[.inl 2,.inr (1,false),.inr (2,true),.inr (3,false)]),
    (1,[.inr (0,true),.inl 1,.inr (5,true),.inr (4,false)]),
    (0,[.inr (1,true),.inl 3,.inr (4,true),.inr (5,false)])] := rfl

theorem template_edges : template.edges=[0,0,0,0,0,0] := rfl

theorem counts : (network f g).shape.vertices=4 ∧ (network f g).shape.edges=6 ∧
    template.vertices.length=4 ∧ template.edges.length=6 := ⟨rfl,rfl,rfl,rfl⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneGramGraph
