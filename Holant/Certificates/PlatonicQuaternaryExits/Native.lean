import Holant.Certificates.OctahedralSeparator.NativeOrder
import Holant.Certificates.OctahedralSeparator.GroupMembership

/-! Direct quaternary exit graphs: the one original four-port label remains a
vertex. Four leg binaries, or two leg binaries and one pair binary, are joined
by literal native X edges. This does not reuse a six-port ancestor realization. -/
namespace Holant.Certificates.PlatonicQuaternaryExits
open Holant
open Holant.Certificates.OctahedralSeparator (nativeTransfer)
open Holant.Certificates.OctahedralSeparator.Native (Binary binarySignature pairVertex legVertex)
noncomputable section
set_option backward.isDefEq.respectTransparency false

abbrev Direction := Matrix Bool Bool ℂ → Prop

def resources (D : Direction) (q : Signature ℂ 4) : SignatureFamily ℂ :=
  {s | s=⟨4,q⟩ ∨ ∃ U : Binary, s=⟨2,binarySignature U⟩ ∧ D (nativeTransfer U)}

/-- Exact denotation, actual binary transfers, exactly one original q vertex,
and at most four binary vertices are all obligations of this predicate. -/
def BoundedRealization {n : ℕ} (D : Direction) (q : Signature ℂ 4)
    (t : Signature ℂ n) : Prop :=
  ∃ N : Network ℂ n, N.denote=t ∧
    (∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature ℂ) ∈ resources D q) ∧
    (∀ e, N.edge e=Signature.disequality) ∧
    (Finset.univ.filter (fun v => N.shape.arity v=4)).card=1 ∧
    (Finset.univ.filter (fun v => N.shape.arity v=2)).card≤4

theorem BoundedRealization.realizes {n : ℕ} {D : Direction} {q : Signature ℂ 4}
    {t : Signature ℂ n} (h : BoundedRealization D q t) :
    Gadget.Realizes (resources D q) .disequality t := by
  obtain ⟨N,ht,hv,he,_,_⟩ := h
  have hr := Gadget.realizes_network N (resources D q) .disequality hv he
  rwa [ht] at hr

namespace Native

def dressedArity : Fin 5 → ℕ := Fin.cases 4 (fun _ => 2)
def dressedPortMap : (Σ v : Fin 5, Fin (dressedArity v)) → (Fin 4 ⊕ (Fin 4 × Bool)) := fun p =>
  Fin.cases (fun i => .inr (i,false))
    (fun j => fun i : Fin 2 => if i=0 then .inl j else .inr (j,true)) p.1 p.2
def dressedPortInv : (Fin 4 ⊕ (Fin 4 × Bool)) → (Σ v : Fin 5, Fin (dressedArity v))
  | .inl j => ⟨j.succ,(0 : Fin 2)⟩
  | .inr (e,b) => if b then ⟨e.succ,(1 : Fin 2)⟩ else ⟨0,e⟩
def dressedShape : NetworkShape 4 where
  vertices := 5
  arity := dressedArity
  edges := 4
  ports := {
    toFun := dressedPortMap
    invFun := dressedPortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [dressedArity] at i <;> fin_cases i <;> rfl
    right_inv p := by
      cases p with
      | inl j => fin_cases j <;> rfl
      | inr p => rcases p with ⟨e,b⟩; fin_cases e <;> cases b <;> rfl }
def dressedLabels (q : Signature ℂ 4) (L : Fin 4 → Binary) :
    (v : Fin 5) → Signature ℂ (dressedArity v) :=
  Fin.cases q (fun j => binarySignature (legVertex (L j)))
def dressedNetwork (q : Signature ℂ 4) (L : Fin 4 → Binary) : Network ℂ 4 where
  shape := dressedShape
  vertex := dressedLabels q L
  edge := fun _ => Signature.disequality

def complementChoices : (Fin 4 → Bool) ≃ (Fin 4 → Bool) where
  toFun c := fun j => !(c j)
  invFun c := fun j => !(c j)
  left_inv c := by funext j; simp
  right_inv c := by funext j; simp

theorem dressed_product (q : Signature ℂ 4) (L : Fin 4 → Binary) (x y : Fin 4 → Bool) :
    (∏ v : Fin 5, dressedLabels q L v
      (dressedShape.assignment x (Network.endpointChoiceAssignment (complementChoices.symm y)) v)) =
      (∏ j : Fin 4, L j (x j) (y j))*q y := by
  have ha : dressedShape.assignment x
      (Network.endpointChoiceAssignment (complementChoices.symm y)) (0 : Fin 5)=y := by
    funext j
    simp [dressedShape,NetworkShape.assignment,dressedPortMap,
      Network.endpointChoiceAssignment,complementChoices]
  simp only [dressedShape,Fin.prod_univ_succ]
  change q (dressedShape.assignment x
    (Network.endpointChoiceAssignment (complementChoices.symm y)) (0 : Fin 5))*_= _
  rw [ha]
  change q y*(legVertex (L 0) (x 0) (!(y 0))*(legVertex (L 1) (x 1) (!(y 1))*
    (legVertex (L 2) (x 2) (!(y 2))*(legVertex (L 3) (x 3) (!(y 3))*1))))=_
  simp [OctahedralSeparator.Native.legVertex_edge,Fin.prod_univ_succ,mul_comm,mul_left_comm,mul_assoc]
  left
  ring

theorem dressed_denote (q : Signature ℂ 4) (L : Fin 4 → Binary) :
    (dressedNetwork q L).denote=Signature.coordinateAction L q := by
  rw [dressedNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 4 → Bool, ∏ v : Fin 5, dressedLabels q L v
    (dressedShape.assignment x (Network.endpointChoiceAssignment c) v))=_
  rw [← complementChoices.symm.sum_comp]
  simp_rw [dressed_product]
  rfl

theorem dressed_bounded (D : Direction) (q : Signature ℂ 4) (L : Fin 4 → Binary)
    (hL : ∀ j, D (nativeTransfer (legVertex (L j)))) :
    BoundedRealization D q (Signature.coordinateAction L q) := by
  refine ⟨dressedNetwork q L,dressed_denote q L,?_,by intro e; rfl,?_,?_⟩
  · intro v
    fin_cases v
    · exact Or.inl rfl
    · exact Or.inr ⟨_,rfl,hL 0⟩
    · exact Or.inr ⟨_,rfl,hL 1⟩
    · exact Or.inr ⟨_,rfl,hL 2⟩
    · exact Or.inr ⟨_,rfl,hL 3⟩
  · change (Finset.univ.filter (fun v : Fin 5 => dressedArity v=4)).card=1
    decide
  · change (Finset.univ.filter (fun v : Fin 5 => dressedArity v=2)).card≤4
    decide

def sparseArity : Fin 4 → ℕ := Fin.cases 4 (fun _ => 2)
def sparsePortMap : (Σ v : Fin 4, Fin (sparseArity v)) → (Fin 2 ⊕ (Fin 4 × Bool)) := fun p =>
  Fin.cases (fun i => ![.inr (0,false),.inr (1,false),.inl 0,.inr (2,false)] i)
    (fun v => fun i : Fin 2 =>
      ![![.inr (3,false),.inr (1,true)],![.inl 1,.inr (2,true)],
        ![.inr (0,true),.inr (3,true)]] v i) p.1 p.2

def sparsePortInv : (Fin 2 ⊕ (Fin 4 × Bool)) → (Σ v : Fin 4, Fin (sparseArity v))
  | .inl j => ![⟨0,(2 : Fin 4)⟩,⟨2,(0 : Fin 2)⟩] j
  | .inr (e,b) => if b then
      ![⟨3,(0 : Fin 2)⟩,⟨1,(1 : Fin 2)⟩,⟨2,(1 : Fin 2)⟩,⟨3,(1 : Fin 2)⟩] e
    else ![⟨0,(0 : Fin 4)⟩,⟨0,(1 : Fin 4)⟩,⟨0,(3 : Fin 4)⟩,⟨1,(0 : Fin 2)⟩] e

def sparseShape : NetworkShape 2 where
  vertices := 4
  arity := sparseArity
  edges := 4
  ports := {
    toFun := sparsePortMap
    invFun := sparsePortInv
    left_inv p := by
      rcases p with ⟨v,i⟩
      fin_cases v <;> dsimp [sparseArity] at i <;> fin_cases i <;> rfl
    right_inv p := by
      cases p with
      | inl j => fin_cases j <;> rfl
      | inr p => rcases p with ⟨e,b⟩; fin_cases e <;> cases b <;> rfl }

def sparseLabels (q : Signature ℂ 4) (L1 L3 M : Binary) :
    (v : Fin 4) → Signature ℂ (sparseArity v) :=
  Fin.cases q (fun v =>
    ![binarySignature (legVertex L1),binarySignature (legVertex L3),binarySignature (pairVertex M)] v)
def sparseNetwork (q : Signature ℂ 4) (L1 L3 M : Binary) : Network ℂ 2 where
  shape := sparseShape
  vertex := sparseLabels q L1 L3 M
  edge := fun _ => Signature.disequality

def sparseChoices : (Fin 4 → Bool) ≃ (Bool × Bool × Bool × Bool) where
  toFun c := (!(c 0),!(c 3),!(c 1),!(c 2))
  invFun p := ![!p.1,!p.2.2.1,!p.2.2.2,!p.2.1]
  left_inv c := by funext i; fin_cases i <;> simp
  right_inv p := by rcases p with ⟨u,v,y,z⟩; simp

theorem sparse_product (q : Signature ℂ 4) (L1 L3 M : Binary)
    (x : Fin 2 → Bool) (u v y z : Bool) :
    (∏ w : Fin 4, sparseLabels q L1 L3 M w
      (sparseShape.assignment x
        (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z))) w)) =
      M u v*(L1 v y*L3 (x 1) z*q ![u,y,x 0,z]) := by
  have ha : sparseShape.assignment x
      (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z))) (0 : Fin 4)=
        ![u,y,x 0,z] := by
    funext i
    fin_cases i <;> simp [sparseShape,NetworkShape.assignment,sparsePortMap,
      Network.endpointChoiceAssignment,sparseChoices]
  simp only [sparseShape,Fin.prod_univ_succ]
  change q (sparseShape.assignment x
    (Network.endpointChoiceAssignment (sparseChoices.symm (u,v,y,z))) (0 : Fin 4))*_= _
  rw [ha]
  change q ![u,y,x 0,z]*(legVertex L1 (!(!v)) (!y)*
    (legVertex L3 (x 1) (!z)*(pairVertex M (!u) (!v)*1)))=_
  simp only [Bool.not_not,OctahedralSeparator.Native.pairVertex_edge,
    OctahedralSeparator.Native.legVertex_edge,mul_one]
  ring

theorem sparse_denote (q : Signature ℂ 4) (L1 L3 M : Binary) :
    (sparseNetwork q L1 L3 M).denote=Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3] q) := by
  rw [sparseNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 4 → Bool, ∏ v : Fin 4, sparseLabels q L1 L3 M v
    (sparseShape.assignment x (Network.endpointChoiceAssignment c) v))=_
  rw [← sparseChoices.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [sparse_product]
  simp only [Signature.contract,OctahedralSeparator.Native.sparse_coordinateAction,
    Finset.mul_sum,Fin.cons_zero,Fin.cons_succ]
  rfl

def sparseOrder (p : Equiv.Perm (Fin 4)) : (v : Fin 4) → Equiv.Perm (Fin (sparseArity v)) :=
  Fin.cases p (fun _ => Equiv.refl _)
def orderedSparseNetwork (p : Equiv.Perm (Fin 4)) (q : Signature ℂ 4)
    (L1 L3 M : Binary) : Network ℂ 2 :=
  OctahedralSeparator.Native.reorderVertexPorts
    (sparseNetwork (Tensor.reindex p q) L1 L3 M) (sparseOrder p)

theorem orderedSparse_denote (p : Equiv.Perm (Fin 4)) (q : Signature ℂ 4) (L1 L3 M : Binary) :
    (orderedSparseNetwork p q L1 L3 M).denote=Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3] (Tensor.reindex p q)) := by
  rw [orderedSparseNetwork,OctahedralSeparator.Native.reorderVertexPorts_denote,sparse_denote]

theorem orderedSparse_ancestor (p : Equiv.Perm (Fin 4)) (q : Signature ℂ 4) (L1 L3 M : Binary) :
    (orderedSparseNetwork p q L1 L3 M).vertex (0 : Fin 4)=q := by
  change Tensor.reindex p.symm (Tensor.reindex p q)=q
  exact Tensor.reindex_symm p q

theorem sparse_bounded (D : Direction) (p : Equiv.Perm (Fin 4)) (q : Signature ℂ 4)
    (L1 L3 M : Binary) (h1 : D (nativeTransfer (legVertex L1)))
    (h3 : D (nativeTransfer (legVertex L3))) (hM : D (nativeTransfer (pairVertex M))) :
    BoundedRealization D q (Signature.contract M
      (Signature.coordinateAction ![Signature.equality,L1,Signature.equality,L3] (Tensor.reindex p q))) := by
  refine ⟨orderedSparseNetwork p q L1 L3 M,orderedSparse_denote p q L1 L3 M,?_,by intro e; rfl,?_,?_⟩
  · intro v
    fin_cases v
    · change (⟨4,(orderedSparseNetwork p q L1 L3 M).vertex (0 : Fin 4)⟩ : AnySignature ℂ) ∈ _
      rw [orderedSparse_ancestor]
      exact Or.inl rfl
    · exact Or.inr ⟨_,rfl,h1⟩
    · exact Or.inr ⟨_,rfl,h3⟩
    · exact Or.inr ⟨_,rfl,hM⟩
  · change (Finset.univ.filter (fun v : Fin 4 => sparseArity v=4)).card=1
    decide
  · change (Finset.univ.filter (fun v : Fin 4 => sparseArity v=2)).card≤4
    decide

theorem contract_bounded (D : Direction) (p : Equiv.Perm (Fin 4)) (q : Signature ℂ 4) (M : Binary)
    (hI : D (Matrix.of Signature.equality)) (hM : D (nativeTransfer (pairVertex M))) :
    BoundedRealization D q (Signature.contract M (Tensor.reindex p q)) := by
  have h := sparse_bounded D p q Signature.equality Signature.equality M
    (by simpa only [OctahedralSeparator.nativeTransfer_legVertex] using hI)
    (by simpa only [OctahedralSeparator.nativeTransfer_legVertex] using hI) hM
  have hid : (![Signature.equality,Signature.equality,Signature.equality,Signature.equality] : Fin 4 → Binary)=
      fun _ => Signature.equality := by funext j; fin_cases j <;> rfl
  simpa only [hid,Signature.coordinateAction_equality] using h

end Native
end
end Holant.Certificates.PlatonicQuaternaryExits
