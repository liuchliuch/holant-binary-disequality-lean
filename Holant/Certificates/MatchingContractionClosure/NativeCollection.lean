import Holant.Certificates.MatchingContractionClosure.CollectionClosure
import Holant.OneHot.NetworkBridge.FiniteNative
import Holant.NetworkAsGadget
import Mathlib.Data.Fintype.BigOperators

namespace Holant.Certificates.MatchingContractionClosure
open Holant
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
variable {K E : Type*} [Field K] [Fintype E] [DecidableEq E] {m n : ℕ}

/-- The actual binary vertex between the two native-X wires. -/
def nativePair (C : Binary (K := K)) : Binary (K := K) := X*C*X

theorem nativePair_apply (C : Binary (K := K)) (a b : Bool) :
    nativePair C a b=C (!a) (!b) := by
  cases a <;> cases b <;> simp [nativePair,X,Matrix.mul_apply,Signature.disequality]

theorem nativePair_safe {G : Set (Binary (K := K))} (hG : ProjectiveMatrixGroup G)
    (hX : (X : Binary (K := K)) ∈ G) {C : Binary (K := K)} (hC : SafeBinary G C) :
    SafeBinary G (nativePair C) :=
  SafeBinary.mul hG hX (SafeBinary.mul hG hX (safe_X hG) hC) (safe_X hG)

def binarySignature (C : Binary (K := K)) : Signature K 2 := fun x => C (x 0) (x 1)
def collectionArity (m : ℕ) : Option E → ℕ | none => m | some _ => 2

def nativeCollectionPortMap (p : CollectionPorts (Fin m) (Fin n) E) :
    (Σ v : Option E, Fin (collectionArity m v)) → (Fin n ⊕ ((E × Bool) × Bool))
  | ⟨none,i⟩ => match p.symm i with
      | .inl q => .inl q
      | .inr eb => .inr (eb,false)
  | ⟨some e,i⟩ => Fin.cases (.inr ((e,false),true)) (fun _ => .inr ((e,true),true)) i

def nativeCollectionPortInv (p : CollectionPorts (Fin m) (Fin n) E) :
    (Fin n ⊕ ((E × Bool) × Bool)) → (Σ v : Option E, Fin (collectionArity m v))
  | .inl q => ⟨none,p (.inl q)⟩
  | .inr (eb,false) => ⟨none,p (.inr eb)⟩
  | .inr ((e,b),true) => ⟨some e,if b then (1 : Fin 2) else (0 : Fin 2)⟩

def nativeCollectionPorts (p : CollectionPorts (Fin m) (Fin n) E) :
    (Σ v : Option E, Fin (collectionArity m v)) ≃ (Fin n ⊕ ((E × Bool) × Bool)) where
  toFun := nativeCollectionPortMap p
  invFun := nativeCollectionPortInv p
  left_inv q := by
    rcases q with ⟨v,i⟩
    cases v with
    | none =>
      have hi := p.apply_symm_apply i
      cases hs : p.symm i <;> simp_all [nativeCollectionPortMap,nativeCollectionPortInv]
    | some e => fin_cases i <;> rfl
  right_inv q := by
    rcases q with q | ⟨⟨e,b⟩,z⟩
    · simp [nativeCollectionPortMap,nativeCollectionPortInv]
    · cases z <;> cases b <;> simp [nativeCollectionPortMap,nativeCollectionPortInv] <;> rfl

def nativeCollectionLabels (F : Signature K m) (C : E → Binary (K := K)) :
    (v : Option E) → Signature K (collectionArity m v)
  | none => F
  | some e => binarySignature (nativePair (C e))

def nativeCollectionFinite (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) : FiniteNetwork K (Option E) (E × Bool) n where
  arity := collectionArity m
  ports := nativeCollectionPorts p
  vertex := nativeCollectionLabels F C
  edge := fun _ => Signature.disequality

def nativeCollectionNetwork (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) : Network K n :=
  (nativeCollectionFinite p C F).toNetwork

def nativeChoices : ((E × Bool) → Bool) ≃ (E → Bool × Bool) where
  toFun c e := (!(c (e,false)),!(c (e,true)))
  invFun y q := if q.2 then !(y q.1).2 else !(y q.1).1
  left_inv c := by funext ⟨e,b⟩; cases b <;> simp
  right_inv y := by funext e; apply Prod.ext <;> simp

theorem nativeCollection_ancestor_assignment (p : CollectionPorts (Fin m) (Fin n) E)
    (x : Fin n → Bool) (y : E → Bool × Bool) :
    (fun i : Fin m => Sum.elim x (FiniteNetwork.endpointChoiceAssignment (nativeChoices.symm y))
      (nativeCollectionPorts p ⟨none,i⟩))=collectionAssignment p x y := by
  funext i
  obtain ⟨s,rfl⟩ := p.surjective i
  rcases s with q | ⟨e,b⟩
  · simp [nativeCollectionPorts,nativeCollectionPortMap,collectionAssignment]
  · cases b <;> simp [nativeCollectionPorts,nativeCollectionPortMap,collectionAssignment,
      FiniteNetwork.endpointChoiceAssignment,nativeChoices]

theorem nativeCollection_binary_assignment (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (x : Fin n → Bool) (y : E → Bool × Bool) (e : E) :
    binarySignature (nativePair (C e))
      (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment (nativeChoices.symm y))
        (nativeCollectionPorts p ⟨some e,i⟩))=C e (y e).1 (y e).2 := by
  have ha : (fun i : Fin 2 => Sum.elim x
      (FiniteNetwork.endpointChoiceAssignment (nativeChoices.symm y))
      (nativeCollectionPorts p ⟨some e,i⟩))=![!(y e).1,!(y e).2] := by
    funext i
    fin_cases i <;> rfl
  rw [ha]
  change nativePair (C e) (!(y e).1) (!(y e).2)=_
  rw [nativePair_apply]
  simp

/-- The actual one-ancestor native-X graph has exactly the simultaneous
contraction value. No component, path, or matching certificate is assumed. -/
theorem nativeCollection_denote (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) :
    (nativeCollectionNetwork p C F).denote=contractCollection p C F := by
  letI : DecidableEq (E × Bool) := Classical.decEq (E × Bool)
  rw [nativeCollectionNetwork,FiniteNetwork.denote_toNetwork]
  funext x
  rw [nativeCollectionFinite,FiniteNetwork.denote_disequality_apply]
  let T : ((E × Bool) → Bool) → K := fun c => ∏ v : Option E,
    nativeCollectionLabels F C v (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment c)
      (nativeCollectionPorts p ⟨v,i⟩))
  change (∑ c : (E × Bool) → Bool, T c)=_
  rw [← (nativeChoices (E := E)).symm.sum_comp T]
  change (∑ y : E → Bool × Bool, T (nativeChoices.symm y))=
    ∑ y : E → Bool × Bool, kernelProduct C y*F (collectionAssignment p x y)
  apply Finset.sum_congr rfl
  intro y hy
  dsimp only [T]
  rw [Fintype.prod_option]
  change F (fun i => Sum.elim x (FiniteNetwork.endpointChoiceAssignment (nativeChoices.symm y))
    (nativeCollectionPorts p ⟨none,i⟩)) *
    (∏ e, binarySignature (nativePair (C e)) (fun i =>
      Sum.elim x (FiniteNetwork.endpointChoiceAssignment (nativeChoices.symm y))
        (nativeCollectionPorts p ⟨some e,i⟩))) = _
  rw [nativeCollection_ancestor_assignment]
  simp_rw [nativeCollection_binary_assignment]
  exact mul_comm _ _

theorem nativeCollection_vertices (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) :
    (nativeCollectionNetwork p C F).shape.vertices=Fintype.card E+1 := by
  simp [nativeCollectionNetwork,FiniteNetwork.toNetwork]

theorem nativeCollection_edges (p : CollectionPorts (Fin m) (Fin n) E)
    (C : E → Binary (K := K)) (F : Signature K m) :
    (nativeCollectionNetwork p C F).shape.edges=2*Fintype.card E := by
  simp [nativeCollectionNetwork,FiniteNetwork.toNetwork,Nat.mul_comm]

end
end Holant.Certificates.MatchingContractionClosure
