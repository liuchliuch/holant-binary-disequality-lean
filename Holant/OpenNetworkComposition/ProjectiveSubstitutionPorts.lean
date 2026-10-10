import Holant.OpenNetworkComposition.DisjointTensor
import Holant.OpenNetworkComposition.ProjectiveContraction
import Holant.Dihedral.CompatibleClosure.ActualReindex
import Holant.NetworkAsGadget
import Holant.Certificates.MatchingContractionClosure.EmptyCollection

/-! Actual projective gadget realizability on arbitrary finite port types.
Port changes only reorder actual boundaries. Tensor products retain the original
multipliers, and self-contraction uses the proved wire-circle correction. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.OpenNetworkComposition.ProjectiveSubstitution
open Holant.Certificates.MatchingContractionClosure
variable {K : Type*} [Field K]

/-- A finite enumeration witnesses actual realizability of the named ports. -/
def Actual {P : Type*} (family : SignatureFamily K) (f : Tensor K P) : Prop :=
  ∃ n : ℕ, ∃ e : P ≃ Fin n, Gadget.RealizesUpTo family .disequality (Tensor.reindex e f)

theorem realizesUpTo_reindex {m n : ℕ} (family : SignatureFamily K)
    (e : Fin m ≃ Fin n) (f : Signature K m)
    (hf : Gadget.RealizesUpTo family .disequality f) :
    Gadget.RealizesUpTo family .disequality (Tensor.reindex e f) := by
  have hmn : m=n := by simpa using Fintype.card_congr e
  subst n
  obtain ⟨c,hc,hf⟩ := hf
  refine ⟨c,hc,?_⟩
  exact Dihedral.CompatibleClosure.realizes_reindex family .disequality _ hf e.symm

theorem Actual.of_realizesUpTo {n : ℕ} (family : SignatureFamily K)
    (f : Signature K n) (hf : Gadget.RealizesUpTo family .disequality f) : Actual family f :=
  ⟨n,Equiv.refl _,hf⟩

theorem Actual.of_realizes {n : ℕ} (family : SignatureFamily K)
    (f : Signature K n) (hf : Gadget.Realizes family .disequality f) : Actual family f := by
  apply Actual.of_realizesUpTo
  exact ⟨1,one_ne_zero,by simpa using hf⟩

theorem Actual.reindex {P Q : Type*} {family : SignatureFamily K} {f : Tensor K P}
    (hf : Actual family f) (e : P ≃ Q) : Actual family (Tensor.reindex e f) := by
  obtain ⟨n,d,hd⟩ := hf
  refine ⟨n,e.symm.trans d,?_⟩
  convert hd using 1
  funext x
  simp only [Tensor.reindex,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem Actual.ordered {P : Type*} {n : ℕ} {family : SignatureFamily K} {f : Tensor K P}
    (hf : Actual family f) (e : P ≃ Fin n) :
    Gadget.RealizesUpTo family .disequality (Tensor.reindex e f) := by
  obtain ⟨m,d,hd⟩ := hf
  have h := realizesUpTo_reindex family (d.symm.trans e) _ hd
  convert h using 1
  funext x
  simp only [Tensor.reindex,Equiv.trans_apply,Equiv.symm_apply_apply]

theorem Actual.realizesUpTo {n : ℕ} {family : SignatureFamily K} {f : Signature K n}
    (hf : Actual family f) : Gadget.RealizesUpTo family .disequality f :=
  hf.ordered (Equiv.refl _)

theorem Actual.tensor {P Q : Type*} {family : SignatureFamily K}
    {f : Tensor K P} {g : Tensor K Q} (hf : Actual family f) (hg : Actual family g) :
    Actual family (Tensor.tensor f g) := by
  obtain ⟨m,e,hf⟩ := hf
  obtain ⟨n,d,hg⟩ := hg
  refine ⟨m+n,(Equiv.sumCongr e d).trans finSumFinEquiv,?_⟩
  have h := realizesUpTo_tensor family .disequality _ _ hf hg
  convert h using 1
  funext x
  rfl

/-- Empty tensor products are represented by the empty actual graph. -/
theorem Actual.empty {P : Type*} [IsEmpty P] (family : SignatureFamily K) :
    Actual family (fun _ : P → Bool => (1:K)) := by
  refine ⟨0,Equiv.equivOfIsEmpty P (Fin 0),1,one_ne_zero,?_⟩
  have h := Gadget.realizes_network (Network.empty : Network K 0) family .disequality
    (fun v => Fin.elim0 v) (fun e => Fin.elim0 e)
  convert h using 1
  funext x
  simp [Tensor.reindex]

def sigmaFirst {n : ℕ} (a : Fin (n+1) → ℕ) :
    (Σ v,Fin (a v)) ≃ (Fin (a 0) ⊕ Σ v : Fin n,Fin (a v.succ)) where
  toFun p := Fin.cases (fun i => .inl i) (fun v i => .inr ⟨v,i⟩) p.1 p.2
  invFun p := match p with
    | .inl i => ⟨0,i⟩
    | .inr ⟨v,i⟩ => ⟨v.succ,i⟩
  left_inv p := by rcases p with ⟨v,i⟩; cases v using Fin.cases <;> rfl
  right_inv p := by cases p <;> rfl

/-- Every nullary factor is included in the finite vertex product. -/
theorem Actual.vertexProduct (family : SignatureFamily K) (v : ℕ)
    (a : Fin v → ℕ) (f : (i : Fin v) → Signature K (a i))
    (hf : ∀ i, Gadget.RealizesUpTo family .disequality (f i)) :
    Actual family (fun x : (Σ i,Fin (a i)) → Bool => ∏ i,f i (fun j => x ⟨i,j⟩)) := by
  induction v with
  | zero => simpa using Actual.empty (P := Σ i : Fin 0,Fin (a i)) family
  | succ v ih =>
    have h0 := Actual.of_realizesUpTo family _ (hf 0)
    have hr := ih (fun i => a i.succ) (fun i => f i.succ) (fun i => hf i.succ)
    have h := (h0.tensor hr).reindex (sigmaFirst a).symm
    convert h using 1
    funext x
    simp [Tensor.reindex,Tensor.tensor,sigmaFirst,Fin.prod_univ_succ]

/-- Enumerate a selected pair first, followed by all other original ports. -/
def pairOrder {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) : Fin (n+2) ≃ P where
  toFun := Fin.cases u (Fin.cases v (fun i => (r.symm i).val))
  invFun i := if hi : i=u then 0 else if hj : i=v then 1 else (r ⟨i,hi,hj⟩).succ.succ
  left_inv i := by
    cases i using Fin.cases with
    | zero => simp [Fin.cases]
    | succ i =>
      cases i using Fin.cases with
      | zero =>
        change (if hi : v=u then 0 else if hj : v=v then 1 else _) = 1
        simp [Ne.symm huv]
      | succ i => simp [(r.symm i).property.1,(r.symm i).property.2,Fin.cases]
  right_inv i := by
    by_cases hi : i=u
    · subst i; simp
    · by_cases hj : i=v
      · subst i
        simp only [dite_eq_right hi]
        rfl
      · simp [hi,hj]

@[simp] theorem pairOrder_zero {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) : pairOrder u v huv r 0=u := rfl
@[simp] theorem pairOrder_one {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) : pairOrder u v huv r 1=v := rfl
@[simp] theorem pairOrder_tail {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) (i : Fin n) :
    pairOrder u v huv r i.succ.succ=(r.symm i).val := rfl

theorem contractPair_ordered {P : Type*} [DecidableEq P] (u v : P) (huv : u≠v)
    {n : ℕ} (r : Remaining u v ≃ Fin n) (f : Tensor K P) :
    Tensor.reindex r (contractPair u v Signature.disequality f)=
      Signature.contract Signature.disequality (Tensor.reindex (pairOrder u v huv r).symm f) := by
  funext x
  unfold Tensor.reindex contractPair Signature.contract
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 2
  funext i
  obtain ⟨j,rfl⟩ := (pairOrder u v huv r).surjective i
  rw [Equiv.symm_apply_apply]
  cases j using Fin.cases with
  | zero => simp [insertPair_first huv]
  | succ j =>
    cases j using Fin.cases with
    | zero => simp [insertPair_second]
    | succ j =>
      rw [pairOrder_tail,insertPair_other (r.symm j).property.1 (r.symm j).property.2]
      simp

/-- Native pair closure uses the actual gadget and its projective circle rule. -/
theorem Actual.contractPair {P : Type*} [Fintype P] [DecidableEq P]
    {family : SignatureFamily K} {f : Tensor K P} (hf : Actual family f)
    (u v : P) (huv : u≠v) (htwo : (2:K)≠0) :
    Actual family (contractPair u v Signature.disequality f) := by
  let r := Fintype.equivFin (Remaining u v)
  refine ⟨Fintype.card (Remaining u v),r,?_⟩
  rw [contractPair_ordered u v huv r]
  exact realizesUpTo_contract family _ (hf.ordered (pairOrder u v huv r).symm) htwo

end Holant.OpenNetworkComposition.ProjectiveSubstitution
