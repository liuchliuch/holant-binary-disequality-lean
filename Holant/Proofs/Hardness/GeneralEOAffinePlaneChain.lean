import Holant.Proofs.Hardness.EOBinaryPlaneCore
import Holant.Proofs.Hardness.LabelledNetwork

/-! Actual crossed two-wire chains of EO-plane quaternary vertices. The
crossing joins L2 to R1 and L3 to R0 with native X edges. Thus compressed
matrix multiplication has no intervening bit flip. Every original vertex,
its local port order, and its label survive both contractions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChain
open Holant Holant.Complexity
open scoped Matrix
namespace C
export BinaryInterpolation.Chains (tensor tensor_denote reindex reindex_denote Uses Native)
end C
namespace B
export EOBinaryPlaneCore (lift)
end B
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K]

abbrev Mat := Matrix (Fin 2) (Fin 2) K

def bitIndex (b : Bool) : Fin 2 := if b then 1 else 0

def binary (A : Mat (K:=K)) : Signature K 2 := fun x => A (bitIndex (x 0)) (bitIndex (x 1))

def table (f : Signature K 2) : Mat (K:=K) :=
  !![f ![false,false],f ![false,true];f ![true,false],f ![true,true]]

@[simp] theorem binary_table (f : Signature K 2) : binary (table f)=f := by
  funext x
  have hx : x=![x 0,x 1] := by funext i; fin_cases i <;> rfl
  rw [hx]
  cases x 0 <;> cases x 1 <;> rfl

/-- The boundary before contraction is [L2,R1,L3,R0,L0,L1,R2,R3]. -/
def seriesOrder : Equiv.Perm (Fin 8) where
  toFun := ![4,5,0,2,3,1,6,7]
  invFun := ![2,5,3,4,0,1,6,7]
  left_inv := by decide
  right_inv := by decide

def series (L R : Network K 4) : Network K 4 :=
  ((C.reindex (C.tensor L R) seriesOrder).contract Signature.disequality).contract
    Signature.disequality

@[simp] theorem series_vertices (L R : Network K 4) :
    (series L R).shape.vertices=L.shape.vertices+R.shape.vertices := by
  simp [series,C.reindex]

@[simp] theorem series_edges (L R : Network K 4) :
    (series L R).shape.edges=L.shape.edges+R.shape.edges+2 := by
  simp [series,C.reindex]

theorem series_denote (L R : Network K 4) (A D : Mat (K:=K))
    (hL : L.denote=B.lift (binary A)) (hR : R.denote=B.lift (binary D)) :
    (series L R).denote=B.lift (binary (A*D)) := by
  funext x
  rw [series,Network.denote_contract_disequality,
    Network.denote_contract_disequality,Network.denote_contract_disequality,
    C.reindex_denote,C.tensor_denote,hL,hR]
  change (B.lift (binary A) ![x 0,x 1,false,false] *
      B.lift (binary D) ![true,true,x 2,x 3] +
    B.lift (binary A) ![x 0,x 1,true,false] *
      B.lift (binary D) ![true,false,x 2,x 3]) +
    (B.lift (binary A) ![x 0,x 1,false,true] *
      B.lift (binary D) ![false,true,x 2,x 3] +
    B.lift (binary A) ![x 0,x 1,true,true] *
      B.lift (binary D) ![false,false,x 2,x 3]) = _
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [B.lift,binary,bitIndex,h0,h1,h2,h3,Matrix.mul_apply,Fin.sum_univ_two] <;> ring

theorem series_uses (L R : Network K 4) (F : SignatureFamily K)
    (hL : C.Uses L F) (hR : C.Uses R F) : C.Uses (series L R) F := by
  intro v
  change (⟨_,(Network.tensorFinite L R).vertex (finSumFinEquiv.symm v)⟩ : AnySignature K)∈F
  cases finSumFinEquiv.symm v with
  | inl v => exact hL v
  | inr v => exact hR v

theorem series_native (L R : Network K 4)
    (hL : C.Native L) (hR : C.Native R) : C.Native (series L R) := by
  intro e
  refine Fin.cases ?_ (fun e => ?_) e
  · rfl
  · refine Fin.cases ?_ (fun e => ?_) e
    · rfl
    · change (Network.tensorFinite L R).edge (finSumFinEquiv.symm e)=_
      cases finSumFinEquiv.symm e with
      | inl e => exact hL e
      | inr e => exact hR e

/-- A positive chain of k+1 actual four-port networks. -/
def copies (N : Network K 4) : ℕ → Network K 4
  | 0 => N
  | k+1 => series (copies N k) N

@[simp] theorem copies_vertices (N : Network K 4) (k : ℕ) :
    (copies N k).shape.vertices=(k+1)*N.shape.vertices := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp only [copies,series_vertices,ih,Nat.add_mul,Nat.one_mul]

@[simp] theorem copies_edges (N : Network K 4) (k : ℕ) :
    (copies N k).shape.edges=(k+1)*N.shape.edges+2*k := by
  induction k with
  | zero => simp [copies]
  | succ k ih => simp only [copies,series_edges,ih,Nat.add_mul,Nat.one_mul]; omega

theorem copies_uses (N : Network K 4) (F : SignatureFamily K)
    (hN : C.Uses N F) (k : ℕ) : C.Uses (copies N k) F := by
  induction k with
  | zero => exact hN
  | succ k ih => exact series_uses _ _ F ih hN

theorem copies_native (N : Network K 4) (hN : C.Native N) (k : ℕ) :
    C.Native (copies N k) := by
  induction k with
  | zero => exact hN
  | succ k ih => exact series_native _ _ ih hN

theorem copies_denote (N : Network K 4) (A : Mat (K:=K))
    (hN : N.denote=B.lift (binary A)) (k : ℕ) :
    (copies N k).denote=B.lift (binary (A^(k+1))) := by
  induction k with
  | zero => simpa only [copies,Nat.zero_add,pow_one] using hN
  | succ k ih =>
      rw [copies,series_denote _ _ _ _ ih hN]
      congr 2

/-- All vertices retain the original M label. e changes only the external
port routing of each original corolla. -/
def literal (M : Signature K 4) (e : Equiv.Perm (Fin 4)) (k : ℕ) : Network K 4 :=
  copies (C.reindex (Network.corolla M) e) k

@[simp] theorem literal_vertices (M : Signature K 4) (e : Equiv.Perm (Fin 4)) (k : ℕ) :
    (literal M e k).shape.vertices=k+1 := by simp [literal,C.reindex,Network.corolla]

@[simp] theorem literal_edges (M : Signature K 4) (e : Equiv.Perm (Fin 4)) (k : ℕ) :
    (literal M e k).shape.edges=2*k := by simp [literal,C.reindex,Network.corolla]

theorem literal_native (M : Signature K 4) (e : Equiv.Perm (Fin 4)) (k : ℕ) :
    C.Native (literal M e k) := copies_native _ (fun j => Fin.elim0 j) k

theorem literal_uses (M : Signature K 4) (e : Equiv.Perm (Fin 4))
    (F : SignatureFamily K) (hM : (⟨4,M⟩ : AnySignature K)∈F) (k : ℕ) :
    C.Uses (literal M e k) F := copies_uses _ F (fun _ => hM) k

theorem literal_denote (M : Signature K 4) (e : Equiv.Perm (Fin 4))
    (f : Signature K 2) (hM : Tensor.reindex e M=B.lift f) (k : ℕ) :
    (literal M e k).denote=B.lift (binary (table f^(k+1))) := by
  apply copies_denote
  rw [C.reindex_denote,Network.denote_corolla,binary_table]
  exact hM

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChain
