import Holant.Proofs.Hardness.GeneralEOSignedParityComponents

noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityComponents
open Holant.OneHot.Computable Holant.OneHot.Decomposition
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option Elab.async false

private theorem labels_of_edge {n : ℕ} (links : Links n)
    {a b : Fin (n*2)} (h : (a,b) ∈ (graph links).edges) :
    (graph links).label a = (graph links).label b := by
  obtain ⟨e,he⟩ := List.mem_iff_get.mp h
  apply (graph links).label_eq_of_reachable
  exact .rel _ _ ⟨e,congrArg Prod.fst he,congrArg Prod.snd he⟩

theorem link_labels {n : ℕ} (links : Links n) (q : (Fin n × Fin n) × Bool)
    (hq : q ∈ links) :
    label links q.1.1 false = label links q.1.2 q.2 ∧
    label links q.1.1 true = label links q.1.2 (!q.2) := by
  constructor
  · apply labels_of_edge
    apply List.mem_flatMap.mpr
    exact ⟨q,hq,by simp⟩
  · apply labels_of_edge
    apply List.mem_flatMap.mpr
    exact ⟨q,hq,by simp⟩

theorem label_sign {n : ℕ} (links : Links n) (i : Fin n) :
    label links i (signs links i) = scope links i := by
  unfold signs scope
  by_cases h : label links i true < label links i false
  · simp [h,min_eq_right (le_of_lt h)]
  · simp [h,min_eq_left (le_of_not_gt h)]

def reconstruct {n : ℕ} (links : Links n) (y : Fin (n*2) → Bool) (i : Fin n) : Bool :=
  Bool.xor (signs links i) (y (scope links i))

private theorem swapped_xor {m : ℕ} (a b : Fin m) (h : a ≠ b) (z : Bool) :
    Bool.xor (decide (b<a)) z = Bool.xor (Bool.xor (decide (a<b)) z) true := by
  rcases lt_or_gt_of_ne h with h | h
  · cases z <;> simp [h,not_lt_of_ge (le_of_lt h)]
  · cases z <;> simp [h,not_lt_of_ge (le_of_lt h)]

theorem reconstruct_consistent {n : ℕ} (links : Links n) (hg : Good links)
    (y : Fin (n*2) → Bool) : Consistent links (reconstruct links y) := by
  intro q hq
  obtain ⟨hf,ht⟩ := link_labels links q hq
  rcases q with ⟨⟨i,j⟩,p⟩
  cases p with
  | false =>
    simp only [Bool.not_false] at ht
    simp only at hf
    simp only [reconstruct,scope,signs,hf,ht,Bool.xor_false]
  | true =>
    simp only [Bool.not_true] at ht
    simp only at hf
    simp only [reconstruct,scope,signs,hf,ht]
    rw [min_comm (label links j true)]
    exact swapped_xor (label links j true) (label links j false) (Ne.symm (hg j)) _

def unflip {n : ℕ} (links : Links n) (x : Fin n → Bool) (i : Fin n) : Bool :=
  Bool.xor (signs links i) (x i)

theorem unflip_fiber {n : ℕ} (links : Links n) (x : Fin n → Bool)
    (hx : Consistent links x) : GeneralCSPUnused.FiberConstant (scope links) (unflip links x) := by
  intro i j hij
  have hlabels : (graph links).label (vertex i (signs links i)) =
      (graph links).label (vertex j (signs links j)) := by
    change label links i (signs links i) = label links j (signs links j)
    rw [label_sign,label_sign,hij]
  have hr := ((graph links).label_eq_iff _ _).mp hlabels
  have h := lifted_reachable links x hx hr
  simpa only [lifted_vertex,unflip,Bool.xor_comm] using h

theorem unflip_involutive {n : ℕ} (links : Links n) (x : Fin n → Bool) :
    unflip links (unflip links x) = x := by
  funext i
  unfold unflip
  cases signs links i <;> cases x i <;> rfl

theorem unflip_consistent {n : ℕ} (links : Links n) (hg : Good links)
    (z : Fin n → Bool) (hz : GeneralCSPUnused.FiberConstant (scope links) z) :
    Consistent links (unflip links z) := by
  let p : GeneralCSPUnused.ConsistentAssignment (scope links) ×
      (GeneralCSPUnused.Unused (scope links) → Bool) := (⟨z,hz⟩,fun _ => false)
  let y := (GeneralCSPUnused.assignmentEquiv (scope links)).symm p
  have he : (fun i => y (scope links i)) = z :=
    congrArg (fun t => t.1.val) ((GeneralCSPUnused.assignmentEquiv (scope links)).apply_symm_apply p)
  have h := reconstruct_consistent links hg y
  have hr : reconstruct links y = unflip links z := by
    funext i
    exact congrArg (Bool.xor (signs links i)) (congrFun he i)
  rwa [hr] at h

def consistentEquiv {n : ℕ} (links : Links n) (hg : Good links) :
    GeneralCSPUnused.ConsistentAssignment (scope links) ≃
      {x : Fin n → Bool // Consistent links x} where
  toFun z := ⟨unflip links z.val,unflip_consistent links hg z.val z.property⟩
  invFun x := ⟨unflip links x.val,unflip_fiber links x.val x.property⟩
  left_inv z := Subtype.ext (unflip_involutive links z.val)
  right_inv x := Subtype.ext (unflip_involutive links x.val)

local instance {n : ℕ} (links : Links n) (x : Fin n → Bool) :
    Decidable (Consistent links x) := Classical.propDecidable _

theorem assignment_sum {n : ℕ} (links : Links n) (hg : Good links)
    {K : Type*} [CommSemiring K] (w : (Fin n → Bool) → K) :
    (∑ y : Fin (n*2) → Bool, w (reconstruct links y)) =
      (2:K)^GeneralCSPUnused.unusedCount (scope links) *
        ∑ x : Fin n → Bool, if Consistent links x then w x else 0 := by
  classical
  have h := GeneralCSPUnused.assignment_sum (scope links) (fun z => w (unflip links z))
  change (∑ y : Fin (n*2) → Bool, w (reconstruct links y)) = _ at h
  rw [h]
  congr 1
  calc
    _ = ∑ x : {x : Fin n → Bool // Consistent links x}, w x.val := by
      apply Fintype.sum_equiv (consistentEquiv links hg)
      intro z
      rfl
    _ = _ := by
      rw [←Finset.sum_filter]
      exact (Finset.sum_subtype (p := Consistent links) _ (by intro x; simp) w).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOSignedParityComponents
