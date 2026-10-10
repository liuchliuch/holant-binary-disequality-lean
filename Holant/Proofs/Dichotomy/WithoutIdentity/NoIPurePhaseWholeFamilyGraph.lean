import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseWholeFamilyCore
import Holant.Proofs.Dichotomy.Native.NativeAntiTargetOutput

/-! One genuine native graph tensors every nonzero original row, retaining
nullary scalars. A single phase chart for this graph restricts to the same
chart for every original row. This never exchanges a graph universal with
an existential choice of chart. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyGraph
open NoIPurePhaseWholeFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace T
def tensor {K : Type} [Field K] [Algebra ℚ K] {s m n : ℕ} {a : ℕ→ℕ}
    (H : (i : Fin s)→Signature K (a i.val))
    (N : NativeAntiTargetSource.Output H m) (M : NativeAntiTargetSource.Output H n) :
    NativeAntiTargetSource.Output H (m+n) where
  network:=Holant.Complexity.BinaryInterpolation.Chains.tensor N.network M.network
  labels:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.tensor
    N.network M.network N.labels M.labels
  exact:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.exact_tensor
    N.network M.network N.labels M.labels H N.exact M.exact
  native:=by
    intro e
    change Sum.elim N.network.edge M.network.edge (finSumFinEquiv.symm e)=_
    cases finSumFinEquiv.symm e with
    | inl e=>exact N.native e
    | inr e=>exact M.native e
end T
namespace C
export Holant.Complexity.BinaryInterpolation.Chains (tensor_denote)
end C
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option maxRecDepth 16384
set_option Elab.async false
variable (K : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ K:=K.algebra'
variable {s : ℕ} {a : ℕ→ℕ} (H : (i : Fin s)→Signature K (a i.val))

def row (j : Fin s) : Signature AlgebraicComplex (a j.val):=
  fun z=>(H j z : AlgebraicComplex)

def literal (j : Fin s) : NativeAntiTargetSource.Output H (a j.val) where
  network:=Network.corolla (H j)
  labels:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.corolla H j
  exact:=Holant.LocalDrafts.RemoteWork.HardnessChainV1.LabelledNetwork.exact_corolla H j
  native:=fun e=>Fin.elim0 e

def empty : NativeAntiTargetSource.Output H 0 where
  network:=Network.empty
  labels:={vertex:=Fin.elim0,vertex_arity:=fun v=>Fin.elim0 v,edge:=Fin.elim0}
  exact:=fun v=>Fin.elim0 v
  native:=fun e=>Fin.elim0 e

def bundle : List (Fin s)→Σn,NativeAntiTargetSource.Output H n
  | []=>⟨0,empty K H⟩
  | j::js=>let b:=bundle js
    ⟨a j.val+b.1,T.tensor H (literal K H j) b.2⟩

def value (js : List (Fin s)) : Signature AlgebraicComplex (bundle K H js).1:=
  fun z=>((bundle K H js).2.network.denote z : AlgebraicComplex)

@[simp] theorem value_nil : value K H []=(fun _=>1) := by
  funext z
  simp [value,bundle,empty]

@[simp] theorem value_cons (j : Fin s) (js : List (Fin s)) :
    value K H (j::js)=X.tensor (row K H j) (value K H js) := by
  funext z
  change (((Holant.Complexity.BinaryInterpolation.Chains.tensor
    (Network.corolla (H j)) (bundle K H js).2.network).denote z : K) : AlgebraicComplex)=_
  rw [C.tensor_denote,Network.denote_corolla]
  exact map_mul K.subtype _ _

theorem row_nonzero (j : Fin s) (hn : H j≠0) : row K H j≠0 := by
  intro hz
  apply hn
  funext z
  exact Subtype.ext (congrFun hz z)

theorem value_nonzero (js : List (Fin s)) (hn : ∀j∈js,H j≠0) : value K H js≠0 := by
  induction js with
  | nil=>
      rw [value_nil]
      intro h
      exact one_ne_zero (congrFun h Fin.elim0)
  | cons j js ih=>
      rw [value_cons]
      exact X.tensor_nonzero (row_nonzero K H j (hn j List.mem_cons_self))
        (ih (fun k hk=>hn k (List.mem_cons_of_mem j hk)))

/-- Semantic factor reflection is applied to one actual tensor graph. -/
theorem class_rows (C : EOClass) (r : AlgebraicComplex) (hr : r≠0)
    (js : List (Fin s)) (hn : ∀j∈js,H j≠0)
    (good : C.Holds (twist r (value K H js))) :
    ∀j∈js,C.Holds (twist r (row K H j)) := by
  induction js with
  | nil=>simp
  | cons j js ih=>
      rw [value_cons,twist_tensor] at good
      have tailnz:=value_nonzero K H js (fun k hk=>hn k (List.mem_cons_of_mem j hk))
      have headnz:=row_nonzero K H j (hn j List.mem_cons_self)
      intro k hk
      rcases List.mem_cons.mp hk with rfl|hk
      · exact class_left C (twist_nonzero hr tailnz) good
      · exact ih (fun l hl=>hn l (List.mem_cons_of_mem j hl))
          (class_right C (twist_nonzero hr headnz) good) k hk

def indices : List (Fin s):=by
  classical
  exact (List.finRange s).filter (fun j=>H j≠0)

@[simp] theorem mem_indices (j : Fin s) : j∈indices K H↔H j≠0 := by
  simp [indices]

abbrev whole:=bundle K H (indices K H)
abbrev wholeValue:=value K H (indices K H)

theorem whole_nonzero : wholeValue K H≠0 :=
  value_nonzero K H _ (fun j hj=>(mem_indices K H j).mp hj)

/-- Zero rows are restored directly; nonzero nullary rows were retained in
the same native bundle and hence use exactly the same selected phase. -/
theorem all_rows (C : EOClass) (r : AlgebraicComplex) (hr : r≠0)
    (good : C.Holds (twist r (wholeValue K H))) :
    ∀j,C.Holds (twist r (row K H j)) := by
  intro j
  by_cases hn : H j=0
  · have zero : row K H j=0 := by
      funext z
      simp [row,hn]
    rw [zero,twist_zero]
    exact class_zero C _
  · exact class_rows K H C r hr _ (fun k hk=>(mem_indices K H k).mp hk)
      good j ((mem_indices K H j).mpr hn)

/-- The selected chart index precedes the universal over all original rows. -/
theorem common_chart {α : Type} (phase : α→AlgebraicComplex) (nonzero : ∀i,phase i≠0)
    (good : ∃i,Affine (twist (phase i) (wholeValue K H))) :
    ∃i,∀j,Affine (twist (phase i) (row K H j)) := by
  obtain ⟨i,hi⟩:=good
  exact ⟨i,all_rows K H .affine (phase i) (nonzero i) hi⟩

theorem common_product_chart {α : Type} (phase : α→AlgebraicComplex) (nonzero : ∀i,phase i≠0)
    (good : ∃i,Product (twist (phase i) (wholeValue K H))) :
    ∃i,∀j,Product (twist (phase i) (row K H j)) := by
  obtain ⟨i,hi⟩:=good
  exact ⟨i,all_rows K H .product (phase i) (nonzero i) hi⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseWholeFamilyGraph
end
