import Holant.EightVertex.ProductAnchor.Source
import Holant.Complexity.UniversalPairReduction.Source
import Holant.Holographic
import Holant.Complexity.BinaryInterpolation.Chains.Template
import Holant.Proofs.Algorithms.RingHomRealization


noncomputable section
namespace Holant.LocalDrafts.MainChain.QuaternaryEqualityTerminal
open Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Algebraic Holant.Complexity
open UniversalPairReduction
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev delta {K : Type*} [CommSemiring K] : Signature K 2 :=
  fun x => BinaryTable.delta (x 0) (x 1)
abbrev square {K : Type*} [CommSemiring K] : Signature K 4 :=
  Signature.tensor (delta (K:=K)) delta

/-- Exactly one marked hole and two ordered original q vertices. The two
native edges are oriented from the hole to port 0 of their respective q.
External order is (right1,left1,right2,left2,right3,left3), so its first two
ports are again the original ordered Delta, not its transpose. -/
abbrev Vertex := Unit ⊕ Bool
abbrev arity : Vertex → ℕ
  | .inl _ => 2
  | .inr _ => 4
def port : (Σv : Vertex,Fin (arity v)) → (Fin 6 ⊕ (Bool×Bool))
  | ⟨.inl _,i⟩ => .inr (i==1,false)
  | ⟨.inr false,i⟩ => ![.inr (false,true),.inl 1,.inl 3,.inl 5] i
  | ⟨.inr true,i⟩ => ![.inr (true,true),.inl 0,.inl 2,.inl 4] i
def portInv : (Fin 6 ⊕ (Bool×Bool)) → (Σv : Vertex,Fin (arity v))
  | .inl i => ![⟨.inr true,1⟩,⟨.inr false,1⟩,⟨.inr true,2⟩,
      ⟨.inr false,2⟩,⟨.inr true,3⟩,⟨.inr false,3⟩] i
  | .inr (e,false) => ⟨.inl (),if e then 1 else 0⟩
  | .inr (e,true) => ⟨.inr e,0⟩
def ports : (Σv : Vertex,Fin (arity v)) ≃ (Fin 6 ⊕ (Bool×Bool)) where
  toFun := port
  invFun := portInv
  left_inv := by
    rintro ⟨v,i⟩
    rcases v with u|b
    · cases u; fin_cases i <;> rfl
    · cases b <;> fin_cases i <;> rfl
  right_inv := by
    rintro (i|⟨e,b⟩)
    · fin_cases i <;> rfl
    · cases e <;> cases b <;> rfl

def context {K : Type*} [CommSemiring K] (q : Signature K 4) (hole : Signature K 2) :
    FiniteNetwork K Vertex Bool 6 where
  arity := arity
  ports := ports
  vertex := fun v => match v with
    | .inl _ => hole
    | .inr _ => q
  edge := fun _ => Signature.disequality
def step {K : Type*} [CommSemiring K] (q : Signature K 4) : Network K 6 :=
  (context q delta).toNetwork

def assignments : ((Bool×Bool) → Bool) ≃ (Bool×Bool×Bool×Bool) where
  toFun z := (z (false,false),z (false,true),z (true,false),z (true,true))
  invFun z p := if p.1 then (if p.2 then z.2.2.2 else z.2.2.1)
    else (if p.2 then z.2.1 else z.1)
  left_inv := by intro z; funext p; rcases p with ⟨a,b⟩; cases a <;> cases b <;> rfl
  right_inv := by rintro ⟨a,b,c,d⟩; rfl

/-- Actual assignment-sum evaluation, before imposing any pure-equality
condition. Both native-X flips and the output port permutation are visible. -/
theorem step_value {K : Type*} [CommSemiring K] (q : Signature K 4) (x : Fin 6 → Bool) :
    (step q).denote x=q ![true,x 1,x 3,x 5]*q ![false,x 0,x 2,x 4] := by
  rw [step,FiniteNetwork.denote_toNetwork]
  unfold FiniteNetwork.denote
  let weight : ((Bool×Bool) → Bool) → K := fun z =>
    (∏ v : Vertex, (context q delta).vertex v
      (fun i => Sum.elim x z ((context q delta).ports ⟨v,i⟩))) *
      ∏ e : Bool, (context q delta).edge e (z (e,false)) (z (e,true))
  trans ∑ z, weight z
  · apply Finset.sum_congr
    · ext z; simp
    · intro z hz; rfl
  · letI : Fintype (Bool×Bool×Bool×Bool) :=
      @instFintypeProd Bool (Bool×Bool×Bool) Bool.fintype
        (@instFintypeProd Bool (Bool×Bool) Bool.fintype
          (@instFintypeProd Bool Bool Bool.fintype Bool.fintype))
    rw [←assignments.symm.sum_comp weight]
    simp [weight,context,arity,ports,port,assignments,delta,BinaryTable.delta,
      Fintype.sum_prod_type,Fintype.prod_sum_type,Fintype.prod_bool,
      Signature.disequality]
    rw [mul_comm]
    congr 2 <;> funext i <;> fin_cases i <;> rfl

theorem step_pure (A B : Scalar) :
    (step (ge4 A B (fun _ => false))).denote=
      fun x => (A*B)*Signature.tensor delta square x := by
  funext x
  rw [step_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
    simp [ge4,complementWord,funext_iff,Fin.forall_fin_succ,
      Signature.tensor_apply,delta,square,BinaryTable.delta,h0,h1,h2,h3,h4,h5,mul_comm]

theorem step_vertices {K : Type*} [CommSemiring K] (q : Signature K 4) :
    (step q).shape.vertices=3 := by simp [step,context,FiniteNetwork.toNetwork,Vertex]
theorem step_edges {K : Type*} [CommSemiring K] (q : Signature K 4) :
    (step q).shape.edges=2 := by simp [step,context,FiniteNetwork.toNetwork]

/-- Occurrence identity is structural, even when an original label happens
to equal Delta. Do not count equal tensors as marked-hole occurrences. -/
def holeVertex {K : Type*} [CommSemiring K] (q : Signature K 4) : Fin (step q).shape.vertices :=
  (Fintype.equivFin Vertex) (.inl ())
theorem hole_unique {K : Type*} [CommSemiring K] (q : Signature K 4) :
    ∃!v : Fin (step q).shape.vertices,
      (Fintype.equivFin Vertex).symm v=.inl () := by
  refine ⟨holeVertex q,Equiv.symm_apply_apply _ _,?_⟩
  intro v hv
  exact (Fintype.equivFin Vertex).symm.injective (hv.trans (Equiv.symm_apply_apply _ _).symm)
theorem background_label {K : Type*} [CommSemiring K] (q : Signature K 4)
    (v : Fin (step q).shape.vertices) (hv : v≠holeVertex q) :
    (⟨(step q).shape.arity v,(step q).vertex v⟩ : AnySignature K)=⟨4,q⟩ := by
  change (⟨arity ((Fintype.equivFin Vertex).symm v),
    (context q delta).vertex ((Fintype.equivFin Vertex).symm v)⟩ : AnySignature K)=_
  cases h : (Fintype.equivFin Vertex).symm v with
  | inl u =>
      cases u
      exact (hv ((Fintype.equivFin Vertex).symm.injective
        (h.trans (Equiv.symm_apply_apply _ _).symm))).elim
  | inr b => rfl
theorem native_edges {K : Type*} [CommSemiring K] (q : Signature K 4) :
    ∀e,(step q).edge e=Signature.disequality := fun _ => rfl

/-- The nonzero carrier closure required in pure-ge is an actual one-Delta
self-loop graph. Its value is one, not an assumed nonzero oracle answer. -/
def carrier {K : Type*} [CommSemiring K] : Network K 0 :=
  (Network.corolla (delta (K:=K))).contract Signature.disequality
theorem carrier_value {K : Type*} [CommSemiring K] :
    (carrier (K:=K)).denote Fin.elim0=1 := by
  rw [carrier,Network.denote_contract,Network.denote_corolla]
  simp [Signature.contract,Signature.disequality,delta,BinaryTable.delta]

structure PureStep (q : Signature Scalar 4) where
  left : Scalar
  right : Scalar
  left_ne_zero : left≠0
  right_ne_zero : right≠0
  original : q=ge4 left right (fun _ => false)

theorem pureStep_exists {q : Signature Scalar 4} (hp : PureEquality q) : Nonempty (PureStep q) := by
  obtain ⟨A,B,hA,hB,hq⟩ := hp
  exact ⟨⟨A,B,hA,hB,hq⟩⟩
def pureStep {q : Signature Scalar 4} (hp : PureEquality q) : PureStep q :=
  Classical.choice (pureStep_exists hp)
theorem PureStep.value {q : Signature Scalar 4} (P : PureStep q) :
    (step q).denote=fun x => (P.left*P.right)*Signature.tensor delta square x := by
  conv_lhs => rw [P.original]
  exact step_pure _ _
theorem PureStep.scale_ne_zero {q : Signature Scalar 4} (P : PureStep q) :
    P.left*P.right≠0 := mul_ne_zero P.left_ne_zero P.right_ne_zero

/-- Descend the physical context to its ORIGINAL field: the multiplier is
the product of two original entries. No chosen algebraic root or basis
coefficient is asserted to lie in K. The graph is the same step Q. -/
theorem pure_step_original_field {K : Type*} [Field K] (φ : K →+* Scalar)
    (Q : Signature K 4) (h : PureEquality (RingHomRealization.mapSignature φ Q)) :
    (step Q).denote=(fun x =>
      (Q (fun _ => false)*Q (fun _ => true))*Signature.tensor delta square x) ∧
      Q (fun _ => false)*Q (fun _ => true)≠0 := by
  let P := pureStep h
  have h0 : φ (Q (fun _ => false))=P.left :=
    (congrFun P.original (fun _ => false)).trans (ge4_left _ _ _)
  have h1 : φ (Q (fun _ => true))=P.right := by
    exact (congrFun P.original (fun _ => true)).trans (ge4_right _ _ _)
  refine ⟨?_,mul_ne_zero ?_ ?_⟩
  · funext x
    apply φ.injective
    calc
      φ ((step Q).denote x)=
          (step (RingHomRealization.mapSignature φ Q)).denote x := by
        simp only [step_value,RingHomRealization.mapSignature,map_mul]
      _ = (φ (Q (fun _ => false))*φ (Q (fun _ => true)))*
          Signature.tensor delta square x := by rw [P.value,h0,h1]
      _ = φ ((Q (fun _ => false)*Q (fun _ => true))*Signature.tensor delta square x) := by
        cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
          cases h3 : x 3 <;> cases h4 : x 4 <;> cases h5 : x 5 <;>
          simp [Signature.tensor_apply,delta,square,BinaryTable.delta,map_mul,h0,h1,h2,h3,h4,h5]
  · intro hz
    exact P.left_ne_zero (h0.symm.trans (by rw [hz,map_zero]))
  · intro hz
    exact P.right_ne_zero (h1.symm.trans (by rw [hz,map_zero]))

section WholeFamilyPair
open FixedGadgetSubstitution
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature Scalar (a i.val))
variable {q : Signature Scalar 4} (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature Scalar)=⟨4,q⟩)

def stepLabel : Vertex → Fin (s+1)
  | .inl _ => ⟨s,by omega⟩
  | .inr _ => ⟨j.val,by have := j.isLt; omega⟩
include hj in
theorem stepLabel_signature (v : Vertex) :
    (⟨extendedArity s a (stepLabel j v).val,
      BinaryFamily.signatures G BinaryTable.delta (stepLabel j v)⟩ : AnySignature Scalar)=
        ⟨arity v,(context q delta).vertex v⟩ := by
  cases v with
  | inl u =>
      cases u
      have h : 2=extendedArity s a (stepLabel j (.inl ())).val := by
        simp [stepLabel,extendedArity]
      have hh : BinaryFamily.signatures G BinaryTable.delta (stepLabel j (.inl ())) =
          fun x => delta (fun i => x (Fin.cast h i)) := by
        funext x
        simp [BinaryFamily.signatures,stepLabel,delta]
      exact Sigma.ext h.symm ((heq_of_eq hh).trans (EdgeSubdivision.signature_cast_heq h delta))
  | inr b =>
      have h : a j.val=extendedArity s a (stepLabel j (.inr b)).val := by
        simp [stepLabel,extendedArity,j.isLt]
      have hh : BinaryFamily.signatures G BinaryTable.delta (stepLabel j (.inr b)) =
          fun x => G j (fun i => x (Fin.cast h i)) := by
        funext x
        simp [BinaryFamily.signatures,stepLabel,j.isLt]
      exact (Sigma.ext h.symm ((heq_of_eq hh).trans
        (EdgeSubdivision.signature_cast_heq h (G j)))).trans hj

/-- Explicit original q index and explicit NEW carrier index. No existential
labelling is allowed to relabel the carrier as an equal pre-existing tensor. -/
def stepLabels : Labelling (step q).shape (s+1) 1 (extendedArity s a) where
  vertex v := stepLabel j ((Fintype.equivFin Vertex).symm v)
  vertex_arity v := congrArg Sigma.fst
    (stepLabel_signature G j hj ((Fintype.equivFin Vertex).symm v))
  edge _ := 0

theorem stepLabels_value :
    ((stepLabels G j hj).template.network (stepLabels G j hj).wellFormed
      (BinaryFamily.signatures G BinaryTable.delta) (fun _ => Signature.disequality)).denote=
        (step q).denote := by
  rw [Labelling.denote_template]
  apply Network.denote_congr
  · intro v x
    exact BinaryInterpolation.Chains.signature_cast_apply _ _
      (stepLabel_signature G j hj ((Fintype.equivFin Vertex).symm v)) _ x
  · intro e a b
    rfl

theorem stepLabels_marked (v : Fin (step q).shape.vertices) :
    ((stepLabels G j hj).vertex v).val=s ↔ v=holeVertex q := by
  have hh : ∀u : Vertex, (stepLabel j u).val=s ↔ u=.inl () := by
    rintro (u|b)
    · cases u; simp [stepLabel]
    · simp [stepLabel,Nat.ne_of_lt j.isLt]
  change (stepLabel j ((Fintype.equivFin Vertex).symm v)).val=s ↔ _
  rw [hh]
  constructor
  · intro h
    exact (Fintype.equivFin Vertex).symm.injective
      (h.trans (Equiv.symm_apply_apply _ _).symm)
  · rintro rfl
    exact Equiv.symm_apply_apply _ _
theorem stepLabels_one_carrier :
    (∑v : Fin (step q).shape.vertices,
      if ((stepLabels G j hj).vertex v).val=s then 1 else 0 : ℕ)=1 := by
  simp_rw [stepLabels_marked]
  simp

def algebraic (i : Fin s) (x : Fin (a i.val) → Bool) : IsAlgebraic ℚ (G i x) :=
  Algebra.IsAlgebraic.isAlgebraic _
/-- Actual existing WHOLE-FAMILY one-pair program. Its input promise is
at most one Delta occurrence; it is not unrestricted access to either pin. -/
def onePair : UniversalPairReduction.Source.Reduction G (algebraic G) :=
  Classical.choose (UniversalPairReduction.Source.source_universal_one_pair_reduction G (algebraic G))
theorem onePair_queries : ThreeQuery.AtMostQueries (onePair G).machine 3 :=
  Classical.choose_spec (UniversalPairReduction.Source.source_universal_one_pair_reduction G (algebraic G))
end WholeFamilyPair

section Anchor
/-- One basis for EVERY original vertex, with ordinary equality edges. It
does not claim that this change of coordinates is a native-X gadget. -/
def ordinary (N : Network Scalar 0) (R : InvertibleKernel) : Network Scalar 0 where
  shape := N.shape
  vertex := fun v => R.action (N.vertex v)
  edge := fun _ => Signature.equality

theorem anchor_whole_graph (N : Network Scalar 0) (R : InvertibleKernel)
    (k : Scalar) (hX : ∀e,N.edge e=Signature.disequality)
    (hR : Kernel.pullback Signature.disequality R.inverse=
      fun a b => k*Signature.equality a b) :
    k^N.shape.edges*(ordinary N R).denote Fin.elim0=N.denote Fin.elim0 := by
  have hh := congrFun (Network.denote_holographicTransform N R.inverse R.matrix R.inverse_matrix) Fin.elim0
  rw [←hh]
  simp only [Network.denote,Network.holographicTransform,ordinary]
  simp_rw [hX,hR]
  simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro z _
  dsimp only [InvertibleKernel.action]
  ring

/-- Extracted from the already proved anchor event. The novel consumer is
whole_value: a physical graph identity for ALL labels, not singleton Tract. -/
structure AnchorStep (F : SignatureFamily Scalar) where
  signature : Signature Scalar 4
  basis : InvertibleKernel
  edgeScale : Scalar
  vertexScale : Scalar
  edge_ne_zero : edgeScale≠0
  vertex_ne_zero : vertexScale≠0
  actual : Gadget.Realizes F .disequality signature
  edge_exact : Kernel.pullback Signature.disequality basis.inverse=
    fun a b => edgeScale*Signature.equality a b
  anchor_exact : basis.action signature=fun x => vertexScale*equalityFour x
theorem anchorStep_exists {F : SignatureFamily Scalar} (h : HasEqualityAnchor F) :
    Nonempty (AnchorStep F) := by
  obtain ⟨g,R,k,l,hk,hl,hg,hR,hgR⟩ := h
  exact ⟨⟨g,R,k,l,hk,hl,hg,hR,hgR⟩⟩
def anchorStep {F : SignatureFamily Scalar} (h : HasEqualityAnchor F) : AnchorStep F :=
  Classical.choice (anchorStep_exists h)
theorem AnchorStep.whole_value {F : SignatureFamily Scalar} (A : AnchorStep F)
    (N : Network Scalar 0) (hX : ∀e,N.edge e=Signature.disequality) :
    A.edgeScale^N.shape.edges*(ordinary N A.basis).denote Fin.elim0=N.denote Fin.elim0 :=
  anchor_whole_graph N A.basis A.edgeScale hX A.edge_exact

/-- The same basis is applied to the WHOLE labelled graph. Membership of
the anchor alone is never promoted to a common tractable presentation. -/
theorem AnchorStep.whole_labels {F : SignatureFamily Scalar} (A : AnchorStep F)
    (N : Network Scalar 0)
    (hN : ∀v,(⟨N.shape.arity v,N.vertex v⟩ : AnySignature Scalar)∈F) :
    ∀v,(⟨(ordinary N A.basis).shape.arity v,(ordinary N A.basis).vertex v⟩ :
      AnySignature Scalar)∈familyAction A.basis F := by
  intro v
  exact ⟨⟨N.shape.arity v,N.vertex v⟩,hN v,rfl⟩
end Anchor

/-- Consumes the existing proved product alternative; it is not a decision
procedure and does not assert either a whole-family tractable or hard leaf. -/
theorem continuation_exists {q : Signature Scalar 4} {F : SignatureFamily Scalar}
    (h : PureEquality q ∨ HasEqualityAnchor F) : Nonempty (PureStep q ⊕ AnchorStep F) := by
  rcases h with hp|ha
  · exact ⟨.inl (pureStep hp)⟩
  · exact ⟨.inr (anchorStep ha)⟩
def continuation {q : Signature Scalar 4} {F : SignatureFamily Scalar}
    (h : PureEquality q ∨ HasEqualityAnchor F) : PureStep q ⊕ AnchorStep F :=
  Classical.choice (continuation_exists h)

end Holant.LocalDrafts.MainChain.QuaternaryEqualityTerminal
