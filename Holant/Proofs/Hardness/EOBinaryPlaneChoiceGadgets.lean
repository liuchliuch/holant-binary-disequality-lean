import Holant.Proofs.Hardness.EOBinaryPlaneOpen
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Counting.CircuitSemantics

/-! Literal two-copy original-table gadgets for Hadamard square and row/column
sum weighting. Every graph has two original vertices, two native-X edges, and
four ordered opposite boundary ports. No unary or binary factor is supplied. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneChoiceGadgets
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace B
export EOBinaryPlaneCore (lift)
end B
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

/-- 0=square, 1=row-sum weighting, 2=column-sum weighting. -/
def route (kind : Fin 3) (p : Σ_v : Fin 2,Fin 4) : Fin 4⊕(Fin 2×Bool) :=
  (![![![.inl 0,.inr (0,false),.inl 2,.inr (1,false)],
         ![.inr (0,true),.inl 1,.inr (1,true),.inl 3]],
      ![![.inl 0,.inl 1,.inl 2,.inr (0,false)],
         ![.inr (0,true),.inl 3,.inr (1,false),.inr (1,true)]],
      ![![.inl 0,.inl 1,.inl 2,.inr (0,false)],
         ![.inr (1,false),.inr (1,true),.inr (0,true),.inl 3]]] :
    Fin 3→Fin 2→Fin 4→Fin 4⊕(Fin 2×Bool)) kind p.1 p.2

theorem route_bijective (kind : Fin 3) : Function.Bijective (route kind) := by
  fin_cases kind <;> decide

def shape (kind : Fin 3) : NetworkShape 4 where
  vertices := 2
  arity _ := 4
  edges := 2
  ports := Equiv.ofBijective (route kind) (route_bijective kind)

def network {K : Type*} [Semiring K] (M : Signature K 4) (kind : Fin 3) : Network K 4 where
  shape := shape kind
  vertex _ := M
  edge _ := Signature.disequality

def output {K : Type*} [Semiring K] (f : Signature K 2) (kind : Fin 3) : Signature K 2 := fun z=>
  if kind=0 then f z*f z else
  if kind=1 then f z*(f ![z 1,false]+f ![z 1,true])
  else f z*(f ![false,z 1]+f ![true,z 1])

private theorem sum_two_bits {K : Type*} [CommSemiring K] (W : (Fin 2→Bool)→K) :
    (∑a,W a)=W ![false,false]+W ![false,true]+W ![true,false]+W ![true,true] := by
  rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_cons 1]
  simp_rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_cons 0]
  simp only [Fintype.sum_bool,Finset.univ_unique,Finset.sum_singleton]
  change (W ![true,true]+W ![true,false])+(W ![false,true]+W ![false,false])=_
  ac_rfl

theorem denote_lift {K : Type*} [CommSemiring K] (f : Signature K 2) (kind : Fin 3) :
    (network (B.lift f) kind).denote=B.lift (output f kind) := by
  funext x
  rw [EOBinaryPlaneOpen.native_sum _ (fun _=>rfl)]
  change (∑a : Fin 2→Bool,∏v : Fin 2,
    B.lift f ((shape kind).assignment x (fun e=>if e.2 then !(a e.1) else a e.1) v))=_
  rw [sum_two_bits]
  fin_cases kind <;> cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [Fin.prod_univ_two,B.lift,NetworkShape.assignment,shape,route,
    output,h0,h1,h2,h3]
  all_goals ring

def labels {K : Type*} [Semiring K] (M : Signature K 4) (kind : Fin 3) :
    Labelling (network M kind).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

abbrev template (kind : Fin 3) := (labels (K:=ℚ) (fun _=>0) kind).template

theorem template_valid (kind : Fin 3) : (template kind).WellFormed 1 1 (fun _=>4) :=
  (labels (K:=ℚ) (fun _=>0) kind).wellFormed

theorem counts (kind : Fin 3) : (template kind).boundary=4 ∧
    (template kind).vertices.length=2 ∧ (template kind).edges.length=2 := by
  exact ⟨rfl,List.length_ofFn,List.length_ofFn⟩

theorem template_denote {K : Type*} [CommSemiring K] (f : Signature K 2) (kind : Fin 3) :
    ((template kind).network (template_valid kind) (fun _=>B.lift f)
      (fun _=>Signature.disequality)).denote=B.lift (output f kind) := by
  calc
    _=(network (B.lift f) kind).denote := by
      apply Labelling.denote_template_of_labels (labels (B.lift f) kind) _ _
        (network (B.lift f) kind).vertex (network (B.lift f) kind).edge
      · intro v x; rfl
      · intro e a b; rfl
    _=_ := denote_lift f kind

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneChoiceGadgets
