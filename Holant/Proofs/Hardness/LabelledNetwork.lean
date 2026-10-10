import Holant.Complexity.BinaryInterpolation.Chains.Network
import Holant.Complexity.FixedGadgetSubstitution.TemplateCorrespondence

/-! Explicit label propagation and occurrence counts for existing network
constructors. These definitions retain the actual chosen original labels
through tensor/reindex/contraction; no existential relabelling is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex enumerate)
end Chain

variable {K : Type*} {m n s b : ℕ} {a : ℕ → ℕ}
variable (N : Network K m) (M : Network K n)
variable (L : Labelling N.shape s b a) (R : Labelling M.shape s b a)

/-- Explicit left-first label propagation, matching Chains.tensor exactly. -/
def tensor : Labelling (Chain.tensor N M).shape s b a where
  vertex v := Sum.elim L.vertex R.vertex (finSumFinEquiv.symm v)
  vertex_arity v := by
    change a (Sum.elim L.vertex R.vertex (finSumFinEquiv.symm v)).val=
      Sum.elim N.shape.arity M.shape.arity (finSumFinEquiv.symm v)
    cases finSumFinEquiv.symm v with
    | inl v => exact L.vertex_arity v
    | inr v => exact R.vertex_arity v
  edge e := Sum.elim L.edge R.edge (finSumFinEquiv.symm e)

def reindex (p : Equiv.Perm (Fin m)) : Labelling (Chain.reindex N p).shape s b a where
  vertex := L.vertex
  vertex_arity := L.vertex_arity
  edge := L.edge

def contract {n : ℕ} (N : Network K (n+2))
    (L : Labelling N.shape s b a) (edge : Fin b) (kernel : Kernel K) :
    Labelling (N.contract kernel).shape s b a where
  vertex := L.vertex
  vertex_arity := L.vertex_arity
  edge := Fin.cases edge L.edge

/-- A fixed original corolla label, with its exact arity. -/
def corolla (G : (i : Fin s) → Signature K (a i.val)) (j : Fin s) :
    Labelling (Network.corolla (G j)).shape s b a where
  vertex _ := j
  vertex_arity _ := rfl
  edge e := Fin.elim0 e

/-- Occurrences count vertices, not distinct signatures or projective classes. -/
def count {n : ℕ} {N : Network K n} (L : Labelling N.shape s b a) (j : Fin s) : ℕ :=
  ∑ v, if L.vertex v=j then 1 else 0

theorem count_tensor (j : Fin s) :
    count (tensor N M L R) j=count L j+count R j := by
  unfold count
  calc
    _ = ∑ v : Fin N.shape.vertices ⊕ Fin M.shape.vertices,
        if Sum.elim L.vertex R.vertex v=j then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv finSumFinEquiv.symm
      intro v
      rfl
    _ = _ := by simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

theorem count_reindex (p : Equiv.Perm (Fin m)) (j : Fin s) :
    count (reindex N L p) j=count L j := rfl

theorem count_contract {n : ℕ} (N : Network K (n+2))
    (L : Labelling N.shape s b a) (edge : Fin b) (kernel : Kernel K) (j : Fin s) :
    count (contract N L edge kernel) j=count L j := rfl

theorem count_corolla (G : (i : Fin s) → Signature K (a i.val)) (j k : Fin s) :
    count (corolla (b:=b) G j) k=if j=k then 1 else 0 := by
  by_cases h : j=k <;> simp [count,corolla,Network.corolla,h]

/-- The original labels denote precisely the actual constructor vertices. -/
def Exact {n : ℕ} (G : (i : Fin s) → Signature K (a i.val))
    (N : Network K n) (L : Labelling N.shape s b a) : Prop :=
  ∀ v,(⟨a (L.vertex v).val,G (L.vertex v)⟩ : AnySignature K)=
    ⟨N.shape.arity v,N.vertex v⟩

theorem exact_tensor (G : (i : Fin s) → Signature K (a i.val))
    (hN : Exact G N L) (hM : Exact G M R) : Exact G (Chain.tensor N M) (tensor N M L R) := by
  intro v
  change (⟨a (Sum.elim L.vertex R.vertex (finSumFinEquiv.symm v)).val,
    G (Sum.elim L.vertex R.vertex (finSumFinEquiv.symm v))⟩ : AnySignature K)=
      ⟨(Network.tensorFinite N M).arity (finSumFinEquiv.symm v),
        (Network.tensorFinite N M).vertex (finSumFinEquiv.symm v)⟩
  cases finSumFinEquiv.symm v with
  | inl v => exact hN v
  | inr v => exact hM v

theorem exact_reindex (G : (i : Fin s) → Signature K (a i.val))
    (hN : Exact G N L) (p : Equiv.Perm (Fin m)) :
    Exact G (Chain.reindex N p) (reindex N L p) := hN

theorem exact_contract {n : ℕ} (G : (i : Fin s) → Signature K (a i.val))
    (N : Network K (n+2)) (L : Labelling N.shape s b a)
    (hN : Exact G N L) (edge : Fin b) (kernel : Kernel K) :
    Exact G (N.contract kernel) (contract N L edge kernel) := hN

theorem exact_corolla (G : (i : Fin s) → Signature K (a i.val)) (j : Fin s) :
    Exact G (Network.corolla (G j)) (corolla (b:=b) G j) := fun _ => rfl

private theorem filter_ofFn {A : Type*} (p : A → Bool) {n : ℕ} (f : Fin n → A) :
    ((List.ofFn f).filter p).length=∑ i,if p (f i) then (1 : ℕ) else 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.ofFn_succ,Fin.sum_univ_succ]
      cases hp : p (f 0) <;> simp only [List.filter_cons,hp,Bool.false_eq_true,
        eq_self_iff_true,ite_false,ite_true,List.length_cons,ih,Nat.zero_add]
      omega

/-- Serialized labels have exactly the same occurrence counts. -/
theorem template_count {n : ℕ} {N : Network K n} (L : Labelling N.shape s b a) (j : Fin s) :
    (L.template.vertices.filter (fun row => row.1=j.val)).length=count L j := by
  rw [Labelling.template,filter_ofFn]
  unfold count
  apply Finset.sum_congr rfl
  intro v _
  simp only [decide_eq_true_eq,Fin.ext_iff]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork
