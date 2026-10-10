import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.Source


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates
open Holant Holant.Complexity Holant.Algebraic FixedGadgetSubstitution
open Holant.Certificates.MatchingContractionClosure
open Holant.Complexity.BinaryInterpolation.Chains
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

abbrev clauseArity (v : Fin 2) : ℕ := Fin.cases 4 (fun _ => 2) v
abbrev ClausePorts := (v : Fin 2) × Fin (clauseArity v)

/-- `true`: q0 is joined to pin0. `false`: q2 is joined to pin1.
The q ports which remain are respectively [1,2,3] and [0,1,3].
The remaining pin port is boundary 3 in both cases. -/
abbrev clauseShape (one : Bool) : NetworkShape 4 where
  vertices := 2
  arity := clauseArity
  edges := 1
  ports := {
    toFun := fun p => Fin.cases (motive := fun v => Fin (clauseArity v) → Fin 4 ⊕ (Fin 1 × Bool))
      (fun i : Fin 4 => if one then
        ![Sum.inr (0,false),Sum.inl 0,Sum.inl 1,Sum.inl 2] i
        else ![Sum.inl 0,Sum.inl 1,Sum.inr (0,false),Sum.inl 2] i)
      (fun _ => fun i : Fin 2 => if one then
        ![Sum.inr (0,true),Sum.inl 3] i
        else ![Sum.inl 3,Sum.inr (0,true)] i) p.1 p.2
    invFun := fun p => match p with
      | .inl i => if one then
          (show Fin 4 → ClausePorts from ![⟨0,(1 : Fin 4)⟩,⟨0,(2 : Fin 4)⟩,⟨0,(3 : Fin 4)⟩,⟨1,(1 : Fin 2)⟩]) i
          else (show Fin 4 → ClausePorts from ![⟨0,(0 : Fin 4)⟩,⟨0,(1 : Fin 4)⟩,⟨0,(3 : Fin 4)⟩,⟨1,(0 : Fin 2)⟩]) i
      | .inr (_,b) => if b then
          if one then ⟨1,(0 : Fin 2)⟩ else ⟨1,(1 : Fin 2)⟩
          else if one then ⟨0,(0 : Fin 4)⟩ else ⟨0,(2 : Fin 4)⟩
    left_inv := by
      rintro ⟨v,i⟩
      cases one <;> fin_cases v <;> fin_cases i <;> rfl
    right_inv := by
      intro p
      cases p with
      | inl i => cases one <;> fin_cases i <;> rfl
      | inr p =>
        rcases p with ⟨e,b⟩
        fin_cases e
        cases one <;> cases b <;> rfl }

def clauseNetwork {K : Type*} [CommSemiring K] (one : Bool)
    (q : Signature K 4) (pin : Signature K 2) : Network K 4 where
  shape := clauseShape one
  vertex v := Fin.cases q (fun _ => pin) v
  edge := fun _ => Signature.disequality

/-- Both oriented endpoint bits are genuine independent graph variables. -/
def oneEdgeAssignments : ((Fin 1 × Bool) → Bool) ≃ (Bool × Bool) where
  toFun z := (z (0,false),z (0,true))
  invFun p e := if e.2 then p.2 else p.1
  left_inv := by
    intro z
    funext e
    rcases e with ⟨e,b⟩
    fin_cases e
    cases b <;> rfl
  right_inv := by rintro ⟨a,b⟩; rfl

theorem one_network_sum {K : Type*} [CommSemiring K]
    (q : Signature K 4) (pin : Signature K 2) (t : Word) :
    (clauseNetwork true q pin).denote t =
      q ![false,t 0,t 1,t 2] * pin ![true,t 3] +
      q ![true,t 0,t 1,t 2] * pin ![false,t 3] := by
  have hq (z : (Fin 1 × Bool) → Bool) :
      (clauseShape true).assignment t z 0 = ![z (0,false),t 0,t 1,t 2] := by
    funext i
    fin_cases i <;> rfl
  have hp (z : (Fin 1 × Bool) → Bool) :
      (clauseShape true).assignment t z 1 = ![z (0,true),t 3] := by
    funext i
    fin_cases i <;> rfl
  unfold Network.denote
  simp only [clauseNetwork, Fin.prod_univ_two,Fin.prod_univ_one]
  change (∑ z : (Fin 1 × Bool) → Bool,
    q ((clauseShape true).assignment t z 0) *
      pin ((clauseShape true).assignment t z 1) *
      Signature.disequality (z (0,false)) (z (0,true))) = _
  simp_rw [hq,hp]
  change (∑ z : (Fin 1 × Bool) → Bool,
    q ![z (0,false),t 0,t 1,t 2] * pin ![z (0,true),t 3] *
      Signature.disequality (z (0,false)) (z (0,true))) = _
  rw [← oneEdgeAssignments.symm.sum_comp,Fintype.sum_prod_type]
  simp [oneEdgeAssignments,Fintype.sum_bool,Signature.disequality,add_comm]

theorem two_network_sum {K : Type*} [CommSemiring K]
    (q : Signature K 4) (pin : Signature K 2) (t : Word) :
    (clauseNetwork false q pin).denote t =
      q ![t 0,t 1,false,t 2] * pin ![t 3,true] +
      q ![t 0,t 1,true,t 2] * pin ![t 3,false] := by
  have hq (z : (Fin 1 × Bool) → Bool) :
      (clauseShape false).assignment t z 0 = ![t 0,t 1,z (0,false),t 2] := by
    funext i
    fin_cases i <;> rfl
  have hp (z : (Fin 1 × Bool) → Bool) :
      (clauseShape false).assignment t z 1 = ![t 3,z (0,true)] := by
    funext i
    fin_cases i <;> rfl
  unfold Network.denote
  simp only [clauseNetwork, Fin.prod_univ_two,Fin.prod_univ_one]
  change (∑ z : (Fin 1 × Bool) → Bool,
    q ((clauseShape false).assignment t z 0) *
      pin ((clauseShape false).assignment t z 1) *
      Signature.disequality (z (0,false)) (z (0,true))) = _
  simp_rw [hq,hp]
  change (∑ z : (Fin 1 × Bool) → Bool,
    q ![t 0,t 1,z (0,false),t 2] * pin ![t 3,z (0,true)] *
      Signature.disequality (z (0,false)) (z (0,true))) = _
  rw [← oneEdgeAssignments.symm.sum_comp,Fintype.sum_prod_type]
  simp [oneEdgeAssignments,Fintype.sum_bool,Signature.disequality,add_comm]

/-- No projective factor is omitted: native X and the literal 01 table have
coefficient one at their unique compatible assignment. -/
theorem one_network_pin {K : Type*} [CommSemiring K]
    (q : Signature K 4) (t : Word) :
    (clauseNetwork true q (fun x => weightedX 1 0 (x 0) (x 1))).denote t =
      if t 3 then q ![true,t 0,t 1,t 2] else 0 := by
  rw [one_network_sum]
  cases h : t 3 <;> simp [weightedX,h]

theorem two_network_pin {K : Type*} [CommSemiring K]
    (q : Signature K 4) (t : Word) :
    (clauseNetwork false q (fun x => weightedX 1 0 (x 0) (x 1))).denote t =
      if t 3 then 0 else q ![t 0,t 1,false,t 2] := by
  rw [two_network_sum]
  cases h : t 3 <;> simp [weightedX,h]

def exactlyOne (x : Fin 3 → Bool) : Prop :=
  x = ![true,false,false] ∨ x = ![false,true,false] ∨ x = ![false,false,true]
def exactlyTwo (x : Fin 3 → Bool) : Prop :=
  x = ![false,true,true] ∨ x = ![true,false,true] ∨ x = ![true,true,false]

theorem triple_eq_iff (x y : Fin 3 → Bool) :
    x = y ↔ x 0 = y 0 ∧ x 1 = y 1 ∧ x 2 = y 2 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2⟩
  · rintro ⟨h0,h1,h2⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2

def oneClause {K : Type*} [Zero K] (a b c : K) : Signature K 4 := fun t =>
  if t 3 then
    match t 0,t 1,t 2 with
    | true,false,false => a
    | false,true,false => b
    | false,false,true => c
    | _,_,_ => 0
  else 0
def twoClause {K : Type*} [Zero K] (a b c : K) : Signature K 4 := fun t =>
  if t 3 then 0 else
    match t 0,t 1,t 2 with
    | false,true,true => a
    | true,false,true => b
    | true,true,false => c
    | _,_,_ => 0

theorem one_sparse {K : Type*} [CommSemiring K] (p : Entries K) :
    (clauseNetwork true (table (sparseEntries p))
      (fun x => weightedX 1 0 (x 0) (x 1))).denote = oneClause (p.a*p.x) (p.d*p.z) (p.c*p.z) := by
  funext t
  rw [one_network_pin]
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [oneClause,table,sparseEntries,h0,h1,h2,h3]

theorem two_sparse {K : Type*} [CommSemiring K] (p : Entries K) :
    (clauseNetwork false (table (sparseEntries p))
      (fun x => weightedX 1 0 (x 0) (x 1))).denote = twoClause (p.c*p.d) (p.c*p.z) (p.a*p.x) := by
  funext t
  rw [two_network_pin]
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [twoClause,table,sparseEntries,h0,h1,h2,h3]

theorem one_support {K : Type*} [Zero K] (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (t : Word) :
    oneClause a b c t ≠ 0 ↔ t 3 = true ∧ exactlyOne ![t 0,t 1,t 2] := by
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [oneClause,exactlyOne,triple_eq_iff,ha,hb,hc,h0,h1,h2,h3]
theorem two_support {K : Type*} [Zero K] (a b c : K)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (t : Word) :
    twoClause a b c t ≠ 0 ↔ t 3 = false ∧ exactlyTwo ![t 0,t 1,t 2] := by
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;> cases h3 : t 3 <;>
    simp [twoClause,exactlyTwo,triple_eq_iff,ha,hb,hc,h0,h1,h2,h3]

/-- Only q (old label 1), literal 01 (old label 2), and X (edge 0).
The labelling serializes the explicit two-vertex shape, without equivFin. -/
def clauseLabelling (one : Bool) : Labelling (clauseShape one) 3 1
    (PQ.A (s:=2) baseArity loopTemplate) where
  vertex v := Fin.cases 1 (fun _ => 2) v
  vertex_arity := by intro v; fin_cases v <;> rfl
  edge := fun _ => 0
def clauseTemplate (one : Bool) : Template := (clauseLabelling one).template
theorem clauseTemplate_wellFormed (one : Bool) :
    (clauseTemplate one).WellFormed 3 1 (PQ.A (s:=2) baseArity loopTemplate) :=
  (clauseLabelling one).wellFormed
theorem clauseTemplate_boundary (one : Bool) : (clauseTemplate one).boundary = 4 := rfl

theorem one_records :
    (clauseTemplate true).vertices =
      [(1,[.inr (0,false),.inl 0,.inl 1,.inl 2]),
       (2,[.inr (0,true),.inl 3])] ∧ (clauseTemplate true).edges = [0] := by
  constructor <;> rfl
theorem two_records :
    (clauseTemplate false).vertices =
      [(1,[.inl 0,.inl 1,.inr (0,false),.inl 2]),
       (2,[.inl 3,.inr (0,true)])] ∧ (clauseTemplate false).edges = [0] := by
  constructor <;> rfl

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates
