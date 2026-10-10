import Holant.Proofs.Hardness.AdaptiveEOUnitLocal
import Holant.Proofs.Hardness.SparseUnitLabels

/-! Literal palette0=q,1=pin0,2=pin1 on the actual four-coefficient EO unit networks.
The same-q cube and both of its pinned binaries retain their own occurrences.
No choice-based label recovery can silently swap equal original rows. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitLabels
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace U
export AdaptiveEOUnitLocal (cube binary0 binary1 swap01 unitNetwork)
end U
namespace Old
export SparseUnitLabels
  (arity palette pinLabel pinLabels palette_pin pinNetworkLabels pinNetwork_exact pinNetwork_count
   attachLabels attach_exact attach_count)
end Old
namespace LN
export LabelledNetwork (count reindex Exact exact_reindex count_reindex count_contract count_tensor template_count)
end LN
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (reindex)
end Chain
variable {K : Type*} [Field K] (q : Signature K 4)
abbrev arity := Old.arity
abbrev palette := Old.palette q

def cubeLabels (one : Bool) : Labelling (U.cube q one).shape 3 1 arity where
  vertex v := Sum.elim (fun _ : Fin 1=>(0 : Fin 3)) (fun _ : Fin 1=>Old.pinLabel (!one))
    ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)
  vertex_arity v := by
    change arity (Sum.elim (fun _ : Fin 1=>(0 : Fin 3)) (fun _ : Fin 1=>Old.pinLabel (!one))
      ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)).val=
      Sum.elim (fun _ : Fin 1=>4) (fun _ : Fin 1=>1)
        ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)
    cases (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v with
    | inl v=>rfl
    | inr v=>cases one <;> rfl
  edge _:=0

theorem cube_exact (one : Bool) : LN.Exact (palette q) (U.cube q one) (cubeLabels q one) := by
  intro v
  change (⟨arity (Sum.elim (fun _ : Fin 1=>(0 : Fin 3)) (fun _ : Fin 1=>Old.pinLabel (!one))
      ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)).val,
    palette q (Sum.elim (fun _ : Fin 1=>(0 : Fin 3)) (fun _ : Fin 1=>Old.pinLabel (!one))
      ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v))⟩ : AnySignature K)=
    ⟨(Network.tensorFinite (Network.corolla q)
      (Network.corolla (SparseUnitLocal.pin (!one)))).arity
        ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v),
      (Network.tensorFinite (Network.corolla q)
        (Network.corolla (SparseUnitLocal.pin (!one)))).vertex
          ((Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v)⟩
  cases (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm v with
  | inl v=>rfl
  | inr v=>exact Old.palette_pin q (!one)

theorem cube_pin_count (one b : Bool) :
    LN.count (cubeLabels q one) (Old.pinLabel b)=if b=(!one) then 1 else 0 := by
  unfold LN.count
  calc
    _=∑v : Fin 1 ⊕ Fin 1,
        if Sum.elim (fun _=>(0 : Fin 3)) (fun _=>Old.pinLabel (!one)) v=Old.pinLabel b then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm
      intro v
      rfl
    _=_ := by
      rw [Fintype.sum_sum_type]
      cases one <;> cases b <;> simp [Old.pinLabel]

abbrev binary0Labels (one : Bool) := Old.pinNetworkLabels one
  (Chain.reindex (U.cube q one) U.swap01) (LN.reindex _ (cubeLabels q one) U.swap01)
abbrev binary1Labels (one : Bool) := Old.pinNetworkLabels one (U.cube q one) (cubeLabels q one)

theorem binary0_exact (one : Bool) :
    LN.Exact (palette q) (U.binary0 q one) (binary0Labels q one) :=
  Old.pinNetwork_exact q one _ _ (LN.exact_reindex _ _ _ (cube_exact q one) U.swap01)
theorem binary1_exact (one : Bool) :
    LN.Exact (palette q) (U.binary1 q one) (binary1Labels q one) :=
  Old.pinNetwork_exact q one _ _ (cube_exact q one)

theorem binary0_pin_count (one b : Bool) : LN.count (binary0Labels q one) (Old.pinLabel b)=1 := by
  rw [binary0Labels,Old.pinNetwork_count,LN.count_reindex,cube_pin_count]
  cases one <;> cases b <;> rfl
theorem binary1_pin_count (one b : Bool) : LN.count (binary1Labels q one) (Old.pinLabel b)=1 := by
  rw [binary1Labels,Old.pinNetwork_count,cube_pin_count]
  cases one <;> cases b <;> rfl

def labels (one : Bool) : Labelling (U.unitNetwork q one).shape 3 1 arity :=
  Old.attachLabels _ _ (Old.attachLabels _ _ (cubeLabels q one) (binary0Labels q one) 0)
    (binary1Labels q one) 1

theorem labels_exact (one : Bool) : LN.Exact (palette q) (U.unitNetwork q one) (labels q one) :=
  Old.attach_exact q _ _ _ _
    (Old.attach_exact q _ _ _ _ (cube_exact q one) (binary0_exact q one) 0)
    (binary1_exact q one) 1

theorem labels_pin_count (one b : Bool) :
    LN.count (labels q one) (Old.pinLabel b)=if b=(!one) then 3 else 2 := by
  rw [labels,Old.attach_count,Old.attach_count,binary0_pin_count,binary1_pin_count,cube_pin_count]
  cases one <;> cases b <;> rfl

abbrev template (one : Bool) := (labels q one).template

theorem template_valid (one : Bool) : (template q one).WellFormed 3 1 arity := (labels q one).wellFormed

theorem template_pin_count (one b : Bool) :
    ((template q one).vertices.filter (fun row=>row.1=1+b.toNat)).length=if b=(!one) then 3 else 2 := by
  have h := (LN.template_count (labels q one) (Old.pinLabel b)).trans (labels_pin_count q one b)
  cases b <;> exact h


theorem cube_original_count (one : Bool) : LN.count (cubeLabels q one) (0 : Fin 3)=1 := by
  unfold LN.count
  calc
    _=∑v : Fin 1 ⊕ Fin 1,
        if Sum.elim (fun _=>(0 : Fin 3)) (fun _=>Old.pinLabel (!one)) v=0 then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv (Fintype.equivFin (Fin 1 ⊕ Fin 1)).symm
      intro v
      rfl
    _=_ := by
      rw [Fintype.sum_sum_type]
      cases one <;> simp [Old.pinLabel]

private theorem pin_original_count (b : Bool) : LN.count (Old.pinLabels (K:=K) b) (0 : Fin 3)=0 := by
  cases b <;> simp [LN.count,Old.pinLabels,Old.pinLabel,Network.corolla]

private theorem pinNetwork_original_count (one : Bool) (N : Network K 3)
    (L : Labelling N.shape 3 1 arity) :
    LN.count (Old.pinNetworkLabels one N L) (0 : Fin 3)=LN.count L (0 : Fin 3) := by
  rw [Old.pinNetworkLabels,LN.count_contract,LN.count_reindex,LN.count_tensor,pin_original_count,Nat.add_zero]

private theorem attach_original_count (N : Network K 3) (B : Network K 2)
    (NL : Labelling N.shape 3 1 arity) (BL : Labelling B.shape 3 1 arity) (i : Fin 3) :
    LN.count (Old.attachLabels N B NL BL i) (0 : Fin 3)=LN.count NL 0+LN.count BL 0 := by
  rw [Old.attachLabels,LN.count_contract,LN.count_reindex,LN.count_tensor]

theorem labels_original_count (one : Bool) : LN.count (labels q one) (0 : Fin 3)=3 := by
  rw [labels,attach_original_count,attach_original_count,binary0Labels,binary1Labels,
    pinNetwork_original_count,pinNetwork_original_count,LN.count_reindex,cube_original_count]

theorem template_original_count (one : Bool) :
    ((template q one).vertices.filter (fun row=>row.1=0)).length=3 :=
  (LN.template_count (labels q one) (0 : Fin 3)).trans (labels_original_count q one)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.AdaptiveEOUnitLabels
