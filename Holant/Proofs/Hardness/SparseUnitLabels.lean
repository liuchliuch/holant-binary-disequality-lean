import Holant.Proofs.Hardness.SparseUnitLocal
import Holant.Proofs.Hardness.PairedPinsSemantics

/-! Explicit labels for the thin original-M unit macros. No existential label
choice: original M is always zero, and pin0/pin1 are always one/two. The same
actual networks retain all eleven vertices and thirteen native-X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitLabels
open Holant Holant.Complexity FixedGadgetSubstitution
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace U
export SparseUnitLocal
  (pin cube pinned pinPorts pinNetwork pinOrder binary third tailOrder attach attachOrder
   swap swapOrder unitNetwork scale unit unit_value)
end U
namespace LN
export LabelledNetwork
  (count tensor reindex contract Exact exact_tensor exact_reindex exact_contract
   count_tensor count_reindex count_contract template_count)
end LN
namespace Chain
export Holant.Complexity.BinaryInterpolation.Chains (tensor reindex)
end Chain

variable {K : Type*} [Field K] (M : Signature K 4)
abbrev arity := PairedPinsRaw.sourceArity 1 (fun _=>4)
abbrev palette := PairedPinsSemantics.sourceSignatures (a:=fun _=>4) (fun _ : Fin 1=>M)
  (PairedPinsSemantics.pin false) (PairedPinsSemantics.pin true)
def pinLabel (b : Bool) : Fin 3 := if b then 2 else 1

theorem palette_pin (b : Bool) : (⟨arity (pinLabel b).val,palette M (pinLabel b)⟩ : AnySignature K)=⟨1,U.pin b⟩ := by
  cases b <;> rfl

def pinLabels (b : Bool) : Labelling (Network.corolla (U.pin (K:=K) b)).shape 3 1 arity where
  vertex _ := pinLabel b
  vertex_arity _ := by cases b <;> rfl
  edge e := Fin.elim0 e

theorem pin_exact (b : Bool) : LN.Exact (palette M) (Network.corolla (U.pin b)) (pinLabels (K:=K) b) :=
  fun _ => palette_pin M b

theorem pin_count (b d : Bool) :
    LN.count (pinLabels (K:=K) b) (pinLabel d)=if b=d then 1 else 0 := by
  cases b <;> cases d <;> simp [LN.count,pinLabels,pinLabel,Network.corolla]

def cubeLabels (one : Bool) : Labelling (U.cube M one).shape 3 1 arity where
  vertex v := Sum.elim (fun _ : Fin 2 => (0 : Fin 3)) (fun _ : Fin 1 => pinLabel (!one))
    ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v)
  vertex_arity v := by
    change arity (Sum.elim (fun _ : Fin 2 => (0 : Fin 3)) (fun _ : Fin 1 => pinLabel (!one))
      ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v)).val=
        Sum.elim (fun _ : Fin 2 => 4) (fun _ : Fin 1 => 1)
          ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v)
    cases (Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v with
    | inl v => rfl
    | inr v => cases one <;> rfl
  edge _ := 0

theorem cube_exact (one : Bool) : LN.Exact (palette M) (U.cube M one) (cubeLabels M one) := by
  intro v
  change (⟨arity (Sum.elim (fun _ : Fin 2 => (0 : Fin 3)) (fun _ : Fin 1 => pinLabel (!one))
      ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v)).val,
    palette M (Sum.elim (fun _ : Fin 2 => (0 : Fin 3)) (fun _ : Fin 1 => pinLabel (!one))
      ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v))⟩ : AnySignature K)=
    ⟨(Network.tensorFinite (nativeChain M) (Network.corolla (U.pin (!one)))).arity
      ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v),
    (Network.tensorFinite (nativeChain M) (Network.corolla (U.pin (!one)))).vertex
      ((Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v)⟩
  cases (Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm v with
  | inl v => rfl
  | inr v => exact palette_pin M (!one)

theorem cube_pin_count (one b : Bool) :
    LN.count (cubeLabels M one) (pinLabel b)=if b=(!one) then 1 else 0 := by
  unfold LN.count
  calc
    _ = ∑ v : Fin 2 ⊕ Fin 1,
        if Sum.elim (fun _ => (0 : Fin 3)) (fun _ => pinLabel (!one)) v=pinLabel b then (1 : ℕ) else 0 := by
      apply Fintype.sum_equiv (Fintype.equivFin (Fin 2 ⊕ Fin 1)).symm
      intro v
      rfl
    _ = _ := by
      rw [Fintype.sum_sum_type]
      cases one <;> cases b <;> simp [pinLabel]

def pinNetworkLabels (one : Bool) (N : Network K 3) (L : Labelling N.shape 3 1 arity) :
    Labelling (U.pinNetwork one N).shape 3 1 arity :=
  LN.contract _ (LN.reindex _ (LN.tensor N _ L (pinLabels (K:=K) one)) U.pinOrder) 0 Signature.disequality

theorem pinNetwork_exact (one : Bool) (N : Network K 3) (L : Labelling N.shape 3 1 arity)
    (hN : LN.Exact (palette M) N L) :
    LN.Exact (palette M) (U.pinNetwork one N) (pinNetworkLabels one N L) :=
  LN.exact_contract _ _ _
    (LN.exact_reindex _ _ _ (LN.exact_tensor _ _ _ _ _ hN (pin_exact M one)) U.pinOrder) 0 Signature.disequality

theorem pinNetwork_count (one : Bool) (N : Network K 3) (L : Labelling N.shape 3 1 arity) (b : Bool) :
    LN.count (pinNetworkLabels one N L) (pinLabel b)=LN.count L (pinLabel b)+(if one=b then 1 else 0) := by
  rw [pinNetworkLabels,LN.count_contract,LN.count_reindex,LN.count_tensor,pin_count]

abbrev binaryLabels (one : Bool) := pinNetworkLabels one (U.cube M one) (cubeLabels M one)
theorem binary_exact (one : Bool) : LN.Exact (palette M) (U.binary M one) (binaryLabels M one) :=
  pinNetwork_exact M one _ _ (cube_exact M one)
theorem binary_pin_count (one b : Bool) : LN.count (binaryLabels M one) (pinLabel b)=1 := by
  rw [binaryLabels,pinNetwork_count,cube_pin_count]
  cases one <;> cases b <;> rfl

abbrev thirdLabels := pinNetworkLabels false (Chain.reindex (U.cube M false) U.tailOrder)
  (LN.reindex _ (cubeLabels M false) U.tailOrder)
theorem third_exact : LN.Exact (palette M) (U.third M) (thirdLabels M) :=
  pinNetwork_exact M false _ _ (LN.exact_reindex _ _ _ (cube_exact M false) U.tailOrder)
theorem third_pin_count (b : Bool) : LN.count (thirdLabels M) (pinLabel b)=1 := by
  rw [thirdLabels,pinNetwork_count,LN.count_reindex,cube_pin_count]
  cases b <;> rfl

def attachLabels (N : Network K 3) (B : Network K 2) (NL : Labelling N.shape 3 1 arity)
    (BL : Labelling B.shape 3 1 arity) (i : Fin 3) : Labelling (U.attach N B i).shape 3 1 arity :=
  LN.contract _ (LN.reindex _ (LN.tensor N B NL BL) (U.attachOrder i)) 0 Signature.disequality

theorem attach_exact (N : Network K 3) (B : Network K 2) (NL : Labelling N.shape 3 1 arity)
    (BL : Labelling B.shape 3 1 arity) (hN : LN.Exact (palette M) N NL) (hB : LN.Exact (palette M) B BL)
    (i : Fin 3) : LN.Exact (palette M) (U.attach N B i) (attachLabels N B NL BL i) :=
  LN.exact_contract _ _ _
    (LN.exact_reindex _ _ _ (LN.exact_tensor _ _ _ _ _ hN hB) (U.attachOrder i)) 0 Signature.disequality

theorem attach_count (N : Network K 3) (B : Network K 2) (NL : Labelling N.shape 3 1 arity)
    (BL : Labelling B.shape 3 1 arity) (i : Fin 3) (b : Bool) :
    LN.count (attachLabels N B NL BL i) (pinLabel b)=LN.count NL (pinLabel b)+LN.count BL (pinLabel b) := by
  rw [attachLabels,LN.count_contract,LN.count_reindex,LN.count_tensor]

def labels (one : Bool) : Labelling (U.unitNetwork M one).shape 3 1 arity := by
  cases one
  · exact attachLabels _ _ (attachLabels _ _ (cubeLabels M false) (thirdLabels M) 0)
      (LN.reindex _ (binaryLabels M false) U.swapOrder) 2
  · exact attachLabels _ _ (attachLabels _ _ (cubeLabels M true) (binaryLabels M false) 0)
      (binaryLabels M true) 1

theorem labels_exact (one : Bool) : LN.Exact (palette M) (U.unitNetwork M one) (labels M one) := by
  cases one
  · exact attach_exact M _ _ _ _ (attach_exact M _ _ _ _ (cube_exact M false) (third_exact M) 0)
      (LN.exact_reindex _ _ _ (binary_exact M false) U.swapOrder) 2
  · exact attach_exact M _ _ _ _ (attach_exact M _ _ _ _ (cube_exact M true) (binary_exact M false) 0)
      (binary_exact M true) 1

theorem labels_pin_count (one b : Bool) : LN.count (labels M one) (pinLabel b)=if b=(!one) then 3 else 2 := by
  cases one <;> simp only [labels,attach_count,LN.count_reindex,binary_pin_count,third_pin_count,cube_pin_count]
  all_goals cases b <;> rfl

abbrev template (one : Bool) := (labels M one).template

theorem template_valid (one : Bool) : (template M one).WellFormed 3 1 arity := (labels M one).wellFormed

theorem template_pin_count (one b : Bool) :
    ((template M one).vertices.filter (fun row => row.1=1+b.toNat)).length=if b=(!one) then 3 else 2 := by
  have h := (LN.template_count (labels M one) (pinLabel b)).trans (labels_pin_count M one b)
  cases b <;> exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.SparseUnitLabels
