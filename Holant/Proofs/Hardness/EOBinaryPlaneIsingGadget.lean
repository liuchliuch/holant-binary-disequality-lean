import Holant.Proofs.Hardness.EOBinaryPlaneOpen
import Holant.Proofs.Hardness.LabelledNetwork
import Holant.Proofs.Counting.CircuitSemantics
import Holant.Proofs.Hardness.BinaryIsingWeights

/-! Two original-g vertices with both argument pairs reversed at the second
copy yield the Ising table g(z)g(!z). The graph has exactly two native-X edges,
four ordered boundary ports, and no supplied unary or binary factors. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsingGadget
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace B
export EOBinaryPlaneCore (lift)
end B
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

def route (p : Σ_v : Fin 2,Fin 4) : Fin 4⊕(Fin 2×Bool) :=
  (![![.inl 0,.inr (0,false),.inl 2,.inr (1,false)],
      ![.inl 1,.inr (0,true),.inl 3,.inr (1,true)]] :
    Fin 2→Fin 4→Fin 4⊕(Fin 2×Bool)) p.1 p.2

theorem route_bijective : Function.Bijective route := by decide

def shape : NetworkShape 4 where
  vertices := 2
  arity _ := 4
  edges := 2
  ports := Equiv.ofBijective route route_bijective

def network {K : Type*} [Semiring K] (M : Signature K 4) : Network K 4 where
  shape := shape
  vertex _ := M
  edge _ := Signature.disequality

def output {K : Type*} [Semiring K] (f : Signature K 2) : Signature K 2 :=
  fun z=>f z*f ![!(z 0),!(z 1)]

def p {K : Type*} [Mul K] (f : Signature K 2) : K := f ![false,false]*f ![true,true]
def q {K : Type*} [Mul K] (f : Signature K 2) : K := f ![false,true]*f ![true,false]

theorem output_table {K : Type*} [CommSemiring K] (f : Signature K 2) :
    output f=BinaryIsingWeights.table (p f) (q f) := by
  funext z
  have hz : z=![z 0,z 1] := by funext j; fin_cases j <;> rfl
  rw [hz]
  cases z 0 <;> cases z 1 <;> simp [output,BinaryIsingWeights.table,BinaryIsingWeights.interaction,p,q,mul_comm]

private theorem sum_two_bits {K : Type*} [CommSemiring K] (W : (Fin 2→Bool)→K) :
    (∑a,W a)=W ![false,false]+W ![false,true]+W ![true,false]+W ![true,true] := by
  rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_cons 1]
  simp_rw [Holant.LocalDrafts.CountingHardness.CircuitSemantics.sum_cons 0]
  simp only [Fintype.sum_bool,Finset.univ_unique,Finset.sum_singleton]
  change (W ![true,true]+W ![true,false])+(W ![false,true]+W ![false,false])=_
  ac_rfl

theorem denote_lift {K : Type*} [CommSemiring K] (f : Signature K 2) :
    (network (B.lift f)).denote=B.lift (output f) := by
  funext x
  rw [EOBinaryPlaneOpen.native_sum _ (fun _=>rfl)]
  change (∑a : Fin 2→Bool,∏v : Fin 2,
    B.lift f ((shape).assignment x (fun e=>if e.2 then !(a e.1) else a e.1) v))=_
  rw [sum_two_bits]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [Fin.prod_univ_two,B.lift,NetworkShape.assignment,shape,route,
    output,h0,h1,h2,h3]

def labels {K : Type*} [Semiring K] (M : Signature K 4) :
    Labelling (network M).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity _ := rfl
  edge _ := 0

abbrev template := (labels (K:=ℚ) (fun _=>0)).template

theorem template_valid : (template).WellFormed 1 1 (fun _=>4) :=
  (labels (K:=ℚ) (fun _=>0)).wellFormed

theorem counts : (template).boundary=4 ∧
    (template).vertices.length=2 ∧ (template).edges.length=2 := by
  exact ⟨rfl,List.length_ofFn,List.length_ofFn⟩

theorem template_denote {K : Type*} [CommSemiring K] (f : Signature K 2) :
    ((template).network (template_valid) (fun _=>B.lift f)
      (fun _=>Signature.disequality)).denote=B.lift (output f) := by
  calc
    _=(network (B.lift f)).denote := by
      apply Labelling.denote_template_of_labels (labels (B.lift f)) _ _
        (network (B.lift f)).vertex (network (B.lift f)).edge
      · intro v x; rfl
      · intro e a b; rfl
    _=_ := denote_lift f

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneIsingGadget
