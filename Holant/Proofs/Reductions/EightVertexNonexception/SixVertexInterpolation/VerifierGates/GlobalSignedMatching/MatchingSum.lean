import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Programs
import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.WeightedMatchingInterpolation.Source
import Holant.Proofs.Reductions.ControlledCap
import Holant.Proofs.Platonic.PhysicalCostCompose


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Source
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines GraphPreprocessing
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype
attribute [local instance] Classical.propDecidable

abbrev Bits (q : Input) := Fin (occurrences q.val).length → Bool
abbrev States (q : Input) := Fin q.val.1 → Cycle.VariableMatching (occurrences q.val).length
def stateEquiv (q : Input) : States q ≃ (Fin q.val.1 → Bool) :=
  Equiv.piCongrRight (fun _ => Cycle.variableEquiv (occurrences q.val).length)
def variableAt (q : Input) (j : Fin (occurrences q.val).length) : Fin q.val.1 :=
  ⟨(occurrence q.val j.val).2.1,occurrence_variable q.val q.property j.val j.isLt⟩
def slotAt (q : Input) (j : Fin (occurrences q.val).length) : Cycle.Vertex (occurrences q.val).length :=
  ⟨j.val,by omega⟩
def marked (q : Input) (z : States q) : Bits q := fun j =>
  Cycle.marked (z (variableAt q j)) (slotAt q j) (occurrence q.val j.val).2.2
def truth (q : Input) (x : Fin q.val.1 → Bool) : Bits q := fun j =>
  DualRail.VerifierInput.literalEval (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x)
    (occurrence q.val j.val).2
def complement (q : Input) (v : Bits q) : Bits q := fun j => !(v j)

theorem marked_truth (q : Input) (z : States q) : complement q (marked q z)=truth q (stateEquiv q z) := by
  funext j
  rw [complement,marked,Cycle.marked_false,Bool.not_not]
  simp only [truth,DualRail.VerifierInput.literalEval,stateEquiv,Equiv.piCongrRight,
    Equiv.coe_fn_mk,Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend]
  rw [dif_pos (occurrence_variable q.val q.property j.val j.isLt)]
  rfl

/-- All row/column boundary bits are explicit. Unpaired words have NOT
been projected out of the clause's actual matching sum. -/
def boundary (q : Input) (c : ℕ) (v : Bits q) : Cycle.Vertex (occurrences q.val).length → Bool := fun i =>
  if h : i.val<(occurrences q.val).length then
    decide ((occurrence q.val i.val).1=c) && v ⟨i.val,h⟩ else false
def clauses (q : Input) (a b : Bits q) : ℤ :=
  ∏ c : Fin q.val.2.length,Cycle.fullTensor (boundary q c.val a) (boundary q c.val b)
def xors (q : Input) (v a b : Bits q) : ℤ :=
  ∏ j : Fin (occurrences q.val).length,ValiantXor.actualTensor ![v j,a j,v j,b j]

/-- Before any pairing restriction, all FOUR independent physical
connector occupations are retained at every XOR occurrence. -/
def allXors (q : Input) (a b c d : Bits q) : ℤ :=
  ∏ j : Fin (occurrences q.val).length,ValiantXor.actualTensor ![a j,b j,c j,d j]
theorem xor_four (a b c d : Bool) :
    ValiantXor.actualTensor ![a,b,c,d]=
      if c=a ∧ b=(!a) ∧ d=(!a) then 2 else 0 := by
  rw [ValiantXor.actual_tensor_exact]
  cases a <;> cases b <;> cases c <;> cases d <;> rfl
theorem allXors_exact (q : Input) (a b c d : Bits q) :
    allXors q a b c d=
      if c=a ∧ b=complement q a ∧ d=complement q a then 2^(occurrences q.val).length else 0 := by
  classical
  unfold allXors
  simp_rw [xor_four]
  by_cases h : c=a ∧ b=complement q a ∧ d=complement q a
  · rcases h with ⟨rfl,rfl,rfl⟩
    simp [complement]
  · rw [if_neg h]
    have hj : ∃ j,¬(c j=a j ∧ b j=!(a j) ∧ d j=!(a j)) := by
      by_contra hn
      push_neg at hn
      exact h ⟨funext (fun j => (hn j).1),funext (fun j => (hn j).2.1),
        funext (fun j => (hn j).2.2)⟩
    obtain ⟨j,hj⟩ := hj
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

/-- Complete boundary summation eliminates every unpaired word by signed
cancellation. `H` is an arbitrary remaining finite tensor; no truth-table or
matching-count law for it is assumed. This is the summation identity needed
BEFORE proving that the residual variable tensor is a cycle assignment. -/
theorem all_boundary_contract (q : Input) (H : Bits q → Bits q → Bits q → Bits q → ℤ) :
    (∑ a : Bits q,∑ b : Bits q,∑ c : Bits q,∑ d : Bits q,
      allXors q a b c d*H a b c d)=
      2^(occurrences q.val).length*∑ a : Bits q,H a (complement q a) a (complement q a) := by
  classical
  simp_rw [allXors_exact]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_eq_single (complement q a)]
  · rw [Finset.sum_eq_single a]
    · rw [Finset.sum_eq_single (complement q a)]
      · simp
      · intro d _ hd
        simp [hd]
      · simp
    · intro c _ hc
      apply Finset.sum_eq_zero
      intro d _
      simp [hc]
    · simp
  · intro b _ hb
    apply Finset.sum_eq_zero
    intro c _
    apply Finset.sum_eq_zero
    intro d _
    simp [hb]
  · simp

theorem xor_paired (v a b : Bool) :
    ValiantXor.actualTensor ![v,a,v,b]=if a=(!v) ∧ b=(!v) then 2 else 0 := by
  rw [ValiantXor.actual_tensor_exact]
  cases v <;> cases a <;> cases b <;> rfl

/-- A simultaneous product of real XOR sums has one surviving boundary
word. Its scalar is exactly 2 per ORIGINAL occurrence, never 7^m queries. -/
theorem xors_exact (q : Input) (v a b : Bits q) :
    xors q v a b=if a=complement q v ∧ b=complement q v then 2^(occurrences q.val).length else 0 := by
  classical
  unfold xors
  simp_rw [xor_paired]
  by_cases h : a=complement q v ∧ b=complement q v
  · rcases h with ⟨rfl,rfl⟩
    simp [complement]
  · rw [if_neg h]
    have hb : ∃ j,¬(a j=!(v j) ∧ b j=!(v j)) := by
      by_contra hn
      push_neg at hn
      apply h
      exact ⟨funext (fun j => (hn j).1),funext (fun j => (hn j).2)⟩
    obtain ⟨j,hj⟩ := hb
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    exact if_neg hj

theorem xor_contract (q : Input) (v : Bits q) :
    (∑ a : Bits q,∑ b : Bits q,xors q v a b*clauses q a b)=
      2^(occurrences q.val).length*clauses q (complement q v) (complement q v) := by
  classical
  simp_rw [xors_exact]
  rw [Finset.sum_eq_single (complement q v)]
  · rw [Finset.sum_eq_single (complement q v)]
    · simp
    · intro b _ hb
      simp [hb]
    · simp
  · intro a _ ha
    apply Finset.sum_eq_zero
    intro b _
    simp [ha]
  · simp

theorem boundary_satisfied (q : Input) (c : Fin q.val.2.length) (x : Fin q.val.1 → Bool) :
    (∃ i,boundary q c.val (truth q x) i=true) ↔
      DualRail.VerifierInput.clauseEval (q.val.2.getD c.val [])
        (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x)=true := by
  constructor
  · rintro ⟨i,hi⟩
    unfold boundary at hi
    split at hi
    · rename_i hj
      have hc : (occurrence q.val i.val).1=c.val := by simpa using (Bool.and_eq_true_iff.mp hi).1
      have ht : truth q x ⟨i.val,hj⟩=true := (Bool.and_eq_true_iff.mp hi).2
      obtain ⟨d,hd,l,hl,he⟩ := (occurrences_member q.val _).mp (occurrence_member q.val i.val hj)
      have hdc : d=c.val := by simpa only [← he] using hc
      subst d
      apply List.any_eq_true.mpr
      refine ⟨l,hl,?_⟩
      simpa only [truth,← he] using ht
    · contradiction
  · intro hc
    obtain ⟨l,hl,ht⟩ := List.any_eq_true.mp hc
    have hm : (c.val,l)∈occurrences q.val :=
      (occurrences_member q.val _).mpr ⟨c.val,c.isLt,l,hl,rfl⟩
    obtain ⟨j,hj⟩ := List.mem_iff_get.mp hm
    have ho : occurrence q.val j.val=(c.val,l) := by
      simpa only [occurrence,List.getD_eq_getElem _ _ j.isLt,List.get_eq_getElem] using hj
    refine ⟨slotAt q j,?_⟩
    simp [boundary,slotAt,j.isLt,ho,truth,ht]

private theorem formula_product (f : DualRail.VerifierInput.Formula) (ρ : ℕ → Bool) :
    (f.map (fun c => if DualRail.VerifierInput.clauseEval c ρ then (1 : ℤ) else 0)).prod=
      if DualRail.VerifierInput.formulaEval f ρ then 1 else 0 := by
  induction f with
  | nil => rfl
  | cons c f ih =>
    change (if DualRail.VerifierInput.clauseEval c ρ then (1 : ℤ) else 0)*
      (f.map (fun c => if DualRail.VerifierInput.clauseEval c ρ then (1 : ℤ) else 0)).prod=
        if DualRail.VerifierInput.clauseEval c ρ && DualRail.VerifierInput.formulaEval f ρ then 1 else 0
    rw [ih]
    cases DualRail.VerifierInput.clauseEval c ρ <;>
      cases DualRail.VerifierInput.formulaEval f ρ <;> rfl

theorem clauses_truth (q : Input) (x : Fin q.val.1 → Bool) :
    clauses q (truth q x) (truth q x)=
      if DualRail.VerifierInput.accepts q.val x then 1 else 0 := by
  classical
  unfold clauses
  simp_rw [Cycle.paired_tensor,boundary_satisfied]
  have hc (c : Fin q.val.2.length) :
      (if DualRail.VerifierInput.clauseEval (q.val.2.getD c.val [])
        (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x)=true then (1 : ℤ) else 0)=
      (if DualRail.VerifierInput.clauseEval (q.val.2.get c)
        (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x) then 1 else 0) := by
    rw [List.getD_eq_getElem _ _ c.isLt,List.get_eq_getElem]
  simp_rw [hc]
  rw [← Fin.prod_ofFn]
  change (List.ofFn (fun i : Fin q.val.2.length => if DualRail.VerifierInput.clauseEval q.val.2[i] (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x) then (1 : ℤ) else 0)).prod = _
  simp only [Fin.getElem_fin]
  rw [List.ofFn_getElem_eq_map q.val.2 (fun c => if DualRail.VerifierInput.clauseEval c (Holant.LocalDrafts.CountingHardness.NetworkSemantics.extend x) then (1 : ℤ) else 0)]
  exact formula_product q.val.2 _

abbrev FamilyChoice (q : Input) := Fin q.val.1 → Cycle.Choice (occurrences q.val).length
def family (q : Input) (z : States q) : FamilyChoice q := fun v => (z v).val
def markFamily (q : Input) (f : FamilyChoice q) : Bits q := fun j =>
  if (occurrence q.val j.val).2.2 then (f (variableAt q j) (slotAt q j)).1
    else (f (variableAt q j) (slotAt q j)).2

/-- Delete exactly the physically replaced cycle occurrence. All other
diagonal/forward edges retain their own selection bit, even at repeated
literal addresses. -/
def erase (q : Input) (f : FamilyChoice q) : FamilyChoice q := fun v i =>
  if h : i.val<(occurrences q.val).length then
    if (occurrence q.val i.val).2.1=v.val then
      if (occurrence q.val i.val).2.2 then (false,(f v i).2) else ((f v i).1,false)
    else f v i
  else f v i

/-- A connector occupation replaces the missing occurrence on the row or
column equation. `a` and `c` will be used independently until XOR cancels
unpaired words; this definition does not make them equal for free. -/
def restore (q : Input) (a : Bits q) (f : FamilyChoice q) : FamilyChoice q := fun v i =>
  if h : i.val<(occurrences q.val).length then
    if (occurrence q.val i.val).2.1=v.val then
      if (occurrence q.val i.val).2.2 then (a ⟨i.val,h⟩,(f v i).2) else ((f v i).1,a ⟨i.val,h⟩)
    else f v i
  else f v i

theorem erase_idem (q : Input) (f : FamilyChoice q) : erase q (erase q f)=erase q f := by
  funext v i
  by_cases hi : i.val<(occurrences q.val).length
  · by_cases hv : (occurrence q.val i.val).2.1=v.val
    · cases hp : (occurrence q.val i.val).2.2 <;> simp [erase,hi,hv,hp]
    · simp [erase,hi,hv]
  · simp [erase,hi]
theorem erase_restore (q : Input) (a : Bits q) (f : FamilyChoice q) :
    erase q (restore q a f)=erase q f := by
  funext v i
  by_cases hi : i.val<(occurrences q.val).length
  · by_cases hv : (occurrence q.val i.val).2.1=v.val
    · cases hp : (occurrence q.val i.val).2.2 <;> simp [erase,restore,hi,hv,hp]
    · simp [erase,restore,hi,hv]
  · simp [erase,restore,hi]
theorem mark_restore (q : Input) (a : Bits q) (f : FamilyChoice q) :
    markFamily q (restore q a f)=a := by
  funext j
  cases hp : (occurrence q.val j.val).2.2 <;>
    simp [markFamily,restore,variableAt,slotAt,j.isLt,hp]
theorem restore_erase_mark (q : Input) (f : FamilyChoice q) :
    restore q (markFamily q f) (erase q f)=f := by
  funext v i
  by_cases hi : i.val<(occurrences q.val).length
  · by_cases hv : (occurrence q.val i.val).2.1=v.val
    · have he : variableAt q ⟨i.val,hi⟩=v := Fin.ext hv
      have hs : slotAt q ⟨i.val,hi⟩=i := Fin.ext rfl
      cases hp : (occurrence q.val i.val).2.2 <;>
        simp [erase,restore,markFamily,hi,hv,hp,he,hs]
    · simp [erase,restore,hi,hv]
  · simp [erase,restore,hi]

/-- The row and column equations of the remaining variable edges, with
the incoming/outgoing connector occupations supplied independently. `erase
f=f` says no deleted occurrence is silently used as an additional edge. -/
def RemainingValid (q : Input) (a c : Bits q) (f : FamilyChoice q) : Prop :=
  erase q f=f ∧
  (∀ v i,Cycle.bit ((restore q a f v i).1)+Cycle.bit ((restore q a f v i).2)=1) ∧
  (∀ v i,Cycle.bit ((restore q c f v (Cycle.next _ i)).1)+Cycle.bit ((restore q c f v i).2)=1)
abbrev RemainingMatching (q : Input) (a c : Bits q) := {f : FamilyChoice q // RemainingValid q a c f}
instance (q : Input) (a c : Bits q) (f : FamilyChoice q) : Decidable (RemainingValid q a c f) := by
  classical
  unfold RemainingValid
  infer_instance
instance (q : Input) (a c : Bits q) : Fintype (RemainingMatching q a c) := by
  classical
  unfold RemainingMatching
  infer_instance
def variableTensor (q : Input) (a c : Bits q) : ℤ := ∑ _f : RemainingMatching q a c,(1 : ℤ)

def restoredState (q : Input) (a : Bits q) (f : RemainingMatching q a a) : States q := fun v =>
  ⟨restore q a f.val v,by
    constructor
    · intro i
      simpa only [Cycle.bit,Cycle.emptyBoundary,Bool.false_eq_true,if_false,Nat.add_zero] using f.property.2.1 v i
    · intro i
      simpa only [Cycle.bit,Cycle.emptyBoundary,Bool.false_eq_true,if_false,Nat.add_zero] using f.property.2.2 v i⟩
theorem restored_mark (q : Input) (a : Bits q) (f : RemainingMatching q a a) :
    marked q (restoredState q a f)=a := by
  exact mark_restore q a f.val
def erasedMatching (q : Input) (z : States q) : RemainingMatching q (marked q z) (marked q z) :=
  ⟨erase q (family q z),by
    have hm : marked q z=markFamily q (family q z) := rfl
    have hr : restore q (marked q z) (erase q (family q z))=family q z := by
      rw [hm,restore_erase_mark]
    refine ⟨erase_idem q _,?_,?_⟩
    · intro v i
      rw [hr]
      simpa only [family,Cycle.bit,Cycle.emptyBoundary,Bool.false_eq_true,if_false,Nat.add_zero] using (z v).property.1 i
    · intro v i
      rw [hr]
      simpa only [family,Cycle.bit,Cycle.emptyBoundary,Bool.false_eq_true,if_false,Nat.add_zero] using (z v).property.2 i⟩

/-- The paired residual variable tensor is recovered from exactly the
original two-choice cycle matching. This proof still preserves BOTH edge
occurrences for an unused variable's one-slot cycle. -/
def remainingEquiv (q : Input) :
    (Σ a : Bits q,RemainingMatching q a a) ≃ States q where
  toFun p := restoredState q p.1 p.2
  invFun z := ⟨marked q z,erasedMatching q z⟩
  left_inv p := by
    have hm := restored_mark q p.1 p.2
    apply Sigma.ext hm
    apply (Subtype.heq_iff_coe_eq (fun f => by dsimp only; rw [hm])).mpr
    exact (erase_restore q p.1 p.2.val).trans p.2.property.1
  right_inv z := by
    funext v
    apply Subtype.ext
    change restore q (marked q z) (erase q (family q z)) v=(z v).val
    change restore q (markFamily q (family q z)) (erase q (family q z)) v=(family q z) v
    rw [restore_erase_mark]

theorem remaining_sum (q : Input) (H : Bits q → ℤ) :
    (∑ a : Bits q,variableTensor q a a*H a)=∑ z : States q,H (marked q z) := by
  unfold variableTensor
  simp_rw [Finset.sum_mul,one_mul]
  rw [← Fintype.sum_sigma (f := fun p : (Σ a : Bits q, RemainingMatching q a a) => H p.1)]
  rw [← (remainingEquiv q).symm.sum_comp (fun p => H p.1)]
  rfl

/-- The graph's block expression BEFORE cancellation. The first and third
vectors are independent variable connector occupations; the second/fourth
are independent clause connector occupations. Every internal variable,
clause, and XOR choice is genuinely summed here. -/
def fullCutValue (q : Input) : ℤ :=
  ∑ a : Bits q,∑ b : Bits q,∑ c : Bits q,∑ d : Bits q,
    allXors q a b c d*(variableTensor q a c*clauses q b d)

/-- This is an explicit CUT contraction, not the cardinality or signed
partition of the flattened raw graph. Each clause still sums over its real
internal exact-one matchings; every XOR uses the delivered full 16-word sum.
-/
def cutValue (q : Input) : ℤ := ∑ z : States q,
  ∑ a : Bits q,∑ b : Bits q,xors q (marked q z) a b*clauses q a b

theorem cut_count (q : Input) :
    cutValue q=2^(occurrences q.val).length*(DualRail.VerifierInput.value q.val : ℤ) := by
  classical
  unfold cutValue
  simp_rw [xor_contract,marked_truth,clauses_truth]
  rw [← Finset.mul_sum,← (stateEquiv q).symm.sum_comp
    (fun z => if DualRail.VerifierInput.accepts q.val (stateEquiv q z) then (1 : ℤ) else 0)]
  simp only [Equiv.apply_symm_apply]
  unfold DualRail.VerifierInput.value Holant.Complexity.countAccepted
  push_cast
  rfl

theorem full_cut_count (q : Input) :
    fullCutValue q=2^(occurrences q.val).length*(DualRail.VerifierInput.value q.val : ℤ) := by
  unfold fullCutValue
  rw [all_boundary_contract,remaining_sum]
  simp_rw [marked_truth,clauses_truth]
  rw [← (stateEquiv q).symm.sum_comp
    (fun z => if DualRail.VerifierInput.accepts q.val (stateEquiv q z) then (1 : ℤ) else 0)]
  simp only [Equiv.apply_symm_apply]
  unfold DualRail.VerifierInput.value Holant.Complexity.countAccepted
  push_cast
  rfl

theorem scalar_nonzero (q : Input) : (2 : ℤ)^(occurrences q.val).length≠0 := pow_ne_zero _ (by decide)
theorem scalar_division (q : Input) :
    (cutValue q : ℚ)/(2 : ℚ)^(occurrences q.val).length=(DualRail.VerifierInput.value q.val : ℚ) := by
  rw [cut_count]
  push_cast
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))
theorem full_scalar_division (q : Input) :
    (fullCutValue q : ℚ)/(2 : ℚ)^(occurrences q.val).length=(DualRail.VerifierInput.value q.val : ℚ) := by
  rw [full_cut_count]
  push_cast
  exact mul_div_cancel_left₀ _ (pow_ne_zero _ (by norm_num))
theorem empty_clause_zero (q : Input) (h : []∈q.val.2) : fullCutValue q=0 := by
  have ha (x : Fin q.val.1 → Bool) : DualRail.VerifierInput.accepts q.val x=false := by
    cases hx : DualRail.VerifierInput.accepts q.val x with
    | false => rfl
    | true =>
      have hall := List.all_eq_true.mp hx [] h
      simp [DualRail.VerifierInput.clauseEval] at hall
  have hv : DualRail.VerifierInput.value q.val=0 := by
    unfold DualRail.VerifierInput.value Holant.Complexity.countAccepted
    simp_rw [ha]
    simp
  rw [full_cut_count,hv]
  simp


end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Source

/-! The selector equivalence below is BEFORE any signed cancellation.
Its edges are occurrence IDs, never endpoint pairs. -/
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.MatchingSum
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype
attribute [local instance] Classical.propDecidable

structure FiniteGraph (R E : Type) where
  left : E → R
  right : E → R
  weight : E → ℤ

variable {R E : Type} [Fintype R] [DecidableEq R] [Fintype E] [DecidableEq E]
def Perfect (G : FiniteGraph R E) (f : R → E) : Prop :=
  (∀ r,G.left (f r)=r) ∧ ∀ c,∃! r,G.right (f r)=c
abbrev Matching (G : FiniteGraph R E) := {f : R → E // Perfect G f}
instance (G : FiniteGraph R E) : Fintype (Matching G) := by
  classical
  unfold Matching
  infer_instance

def Selected (G : FiniteGraph R E) (s : Finset E) : Prop :=
  (∀ r,(s.filter (fun e => G.left e=r)).card=1) ∧
  (∀ c,(s.filter (fun e => G.right e=c)).card=1)
abbrev Selection (G : FiniteGraph R E) := {s : Finset E // Selected G s}
instance (G : FiniteGraph R E) : Fintype (Selection G) := by
  classical
  unfold Selection
  infer_instance
def select (G : FiniteGraph R E) (m : Matching G) : Finset E := Finset.univ.image m.val

theorem matching_injective (G : FiniteGraph R E) (m : Matching G) : Function.Injective m.val := by
  intro r s h
  exact (m.property.1 r).symm.trans ((congrArg G.left h).trans (m.property.1 s))

theorem select_row (G : FiniteGraph R E) (m : Matching G) (r : R) :
    (select G m).filter (fun e => G.left e=r)={m.val r} := by
  ext e
  constructor
  · intro he
    obtain ⟨hmem,hrow⟩ := Finset.mem_filter.mp he
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hmem
    have hsr : s=r := (m.property.1 s).symm.trans (by simpa only [hs] using hrow)
    subst s
    exact Finset.mem_singleton.mpr hs.symm
  · intro he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_image.mpr ⟨r,Finset.mem_univ r,rfl⟩,m.property.1 r⟩

theorem select_column (G : FiniteGraph R E) (m : Matching G) (c : R) :
    ∃ r,(select G m).filter (fun e => G.right e=c)={m.val r} := by
  obtain ⟨r,hr,hu⟩ := m.property.2 c
  refine ⟨r,?_⟩
  ext e
  constructor
  · intro he
    obtain ⟨hmem,hcol⟩ := Finset.mem_filter.mp he
    obtain ⟨s,_,hs⟩ := Finset.mem_image.mp hmem
    have hsr : s=r := hu s (by simpa only [hs] using hcol)
    subst s
    exact Finset.mem_singleton.mpr hs.symm
  · intro he
    obtain rfl := Finset.mem_singleton.mp he
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨r,Finset.mem_univ r,rfl⟩,hr⟩

def toSelection (G : FiniteGraph R E) (m : Matching G) : Selection G :=
  ⟨select G m,by
    constructor
    · intro r; rw [select_row]; simp
    · intro c; obtain ⟨r,hr⟩ := select_column G m c; rw [hr]; simp⟩

def rowEdge (G : FiniteGraph R E) (s : Selection G) (r : R) : E :=
  (Finset.card_eq_one.mp (s.property.1 r)).choose
theorem rowEdge_filter (G : FiniteGraph R E) (s : Selection G) (r : R) :
    s.val.filter (fun e => G.left e=r)={rowEdge G s r} :=
  (Finset.card_eq_one.mp (s.property.1 r)).choose_spec
theorem rowEdge_mem (G : FiniteGraph R E) (s : Selection G) (r : R) :
    rowEdge G s r∈s.val ∧ G.left (rowEdge G s r)=r := by
  have h : rowEdge G s r ∈ s.val.filter (fun e => G.left e = r) := by
    rw [rowEdge_filter]
    exact Finset.mem_singleton_self _
  exact Finset.mem_filter.mp h
theorem rowEdge_unique (G : FiniteGraph R E) (s : Selection G) (r : R) (e : E)
    (he : e∈s.val) (hr : G.left e=r) : rowEdge G s r=e := by
  have h : e∈s.val.filter (fun e => G.left e=r) := Finset.mem_filter.mpr ⟨he,hr⟩
  rw [rowEdge_filter] at h
  exact (Finset.mem_singleton.mp h).symm

def fromSelection (G : FiniteGraph R E) (s : Selection G) : Matching G :=
  ⟨rowEdge G s,by
    refine ⟨fun r => (rowEdge_mem G s r).2,?_⟩
    intro c
    obtain ⟨e,he⟩ := Finset.card_eq_one.mp (s.property.2 c)
    have hem : e∈s.val ∧ G.right e=c := by
      apply Finset.mem_filter.mp
      rw [he]
      exact Finset.mem_singleton_self _
    have hr := rowEdge_unique G s (G.left e) e hem.1 rfl
    refine ⟨G.left e,by dsimp only; rw [hr]; exact hem.2,?_⟩
    intro r hrc
    have hmem : rowEdge G s r∈s.val.filter (fun e => G.right e=c) :=
      Finset.mem_filter.mpr ⟨(rowEdge_mem G s r).1,hrc⟩
    rw [he] at hmem
    have h := congrArg G.left (Finset.mem_singleton.mp hmem)
    exact (rowEdge_mem G s r).2.symm.trans h⟩

def selectionEquiv (G : FiniteGraph R E) : Matching G ≃ Selection G where
  toFun := toSelection G
  invFun := fromSelection G
  left_inv m := by
    apply Subtype.ext
    funext r
    apply rowEdge_unique
    · exact Finset.mem_image.mpr ⟨r,Finset.mem_univ r,rfl⟩
    · exact m.property.1 r
  right_inv s := by
    apply Subtype.ext
    ext e
    constructor
    · intro he
      obtain ⟨r,_,rfl⟩ := Finset.mem_image.mp he
      exact (rowEdge_mem G s r).1
    · intro he
      exact Finset.mem_image.mpr ⟨G.left e,Finset.mem_univ _,
        rowEdge_unique G s _ e he rfl⟩

def selectionWeight (G : FiniteGraph R E) (s : Selection G) : ℤ := ∏ e∈s.val,G.weight e
def matchingWeight (G : FiniteGraph R E) (m : Matching G) : ℤ := ∏ r,G.weight (m.val r)
theorem weight_select (G : FiniteGraph R E) (m : Matching G) :
    selectionWeight G (toSelection G m)=matchingWeight G m := by
  unfold selectionWeight toSelection select matchingWeight
  rw [Finset.prod_image]
  exact fun r _ s _ h => matching_injective G m h

theorem matching_sum_selection (G : FiniteGraph R E) :
    (∑ m : Matching G,matchingWeight G m)=∑ s : Selection G,selectionWeight G s := by
  rw [← (selectionEquiv G).sum_comp (selectionWeight G)]
  exact Finset.sum_congr rfl (fun m _ => (weight_select G m).symm)

def actualLeft (g : WeightedMatchingInterpolation.Input) (e : WeightedMatchingInterpolation.OriginalEdges g) :
    Fin g.val.1 := ⟨(WeightedMatchingInterpolation.originalEdge g e).1.1,
      (g.property _ (List.get_mem g.val.2 e)).1⟩
def actualRight (g : WeightedMatchingInterpolation.Input) (e : WeightedMatchingInterpolation.OriginalEdges g) :
    Fin g.val.1 := ⟨(WeightedMatchingInterpolation.originalEdge g e).1.2,
      (g.property _ (List.get_mem g.val.2 e)).2⟩
def actualGraph (g : WeightedMatchingInterpolation.Input) :
    FiniteGraph (Fin g.val.1) (WeightedMatchingInterpolation.OriginalEdges g) :=
  ⟨actualLeft g,actualRight g,fun e => if (WeightedMatchingInterpolation.originalEdge g e).2 then -1 else 1⟩
def actualMatchingEquiv (g : WeightedMatchingInterpolation.Input) :
    WeightedMatchingInterpolation.Matching g ≃ Matching (actualGraph g) where
  toFun m := ⟨m.val,by
    simpa only [WeightedMatchingInterpolation.Perfect,Perfect,actualGraph,actualLeft,actualRight,Fin.ext_iff] using m.property⟩
  invFun m := ⟨m.val,by
    simpa only [WeightedMatchingInterpolation.Perfect,Perfect,actualGraph,actualLeft,actualRight,Fin.ext_iff] using m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem actual_weight (g : WeightedMatchingInterpolation.Input) (m : WeightedMatchingInterpolation.Matching g) :
    matchingWeight (actualGraph g) (actualMatchingEquiv g m)=
      (-1 : ℤ)^WeightedMatchingInterpolation.negativeCount g m := by
  change (∏ r : Fin g.val.1, if (WeightedMatchingInterpolation.originalEdge g (m.val r)).2 then (-1 : ℤ) else 1) = _
  have he (r : Fin g.val.1) :
      (if (WeightedMatchingInterpolation.originalEdge g (m.val r)).2 then (-1 : ℤ) else 1)=
        (-1 : ℤ)^(if (WeightedMatchingInterpolation.originalEdge g (m.val r)).2 then 1 else 0) := by
    cases h : (WeightedMatchingInterpolation.originalEdge g (m.val r)).2 <;> simp [h]
  simp_rw [he]
  exact Finset.prod_pow_eq_pow_sum _ _ _

/-- Actual original edge-index matching sum, BEFORE cancelling any term. -/
theorem integer_selection_sum (g : WeightedMatchingInterpolation.Input) :
    WeightedMatchingInterpolation.integerValue g=
      ∑ s : Selection (actualGraph g),selectionWeight (actualGraph g) s := by
  rw [← matching_sum_selection,← (actualMatchingEquiv g).sum_comp (matchingWeight (actualGraph g))]
  unfold WeightedMatchingInterpolation.integerValue
  exact Finset.sum_congr rfl (fun m _ => (actual_weight g m).symm)

/-- Four segment tag, original block index, original local slot, branch.
Endpoint pairs are NOT occurrence IDs; equal records can have different IDs.
-/
abbrev KeyID := ℕ × ℕ × ℕ × Bool
def variableKeysBlock (q : Input) (v j : ℕ) : List KeyID :=
  (if isMarked q.val v j false then [] else [(0,v,j,false)]) ++
  (if isMarked q.val v j true then [] else [(0,v,j,true)])
def variableKeys (q : Input) : List KeyID :=
  (List.range q.val.1).flatMap (fun v =>
    (List.range (slots q.val)).flatMap (variableKeysBlock q v))
def clauseKeys (q : Input) : List KeyID :=
  (List.range q.val.2.length).flatMap (fun c =>
    (List.range (slots q.val)).flatMap (fun j => [(1,c,j,false),(1,c,j,true)]))
def xorKeys (q : Input) : List KeyID :=
  (List.range (occurrences q.val).length).flatMap (fun j =>
    (List.range xorLocal.length).map (fun k => (2,j,k,false)))
def connectorKeys (q : Input) : List KeyID :=
  (List.range (occurrences q.val).length).flatMap (fun j =>
    (List.range 4).map (fun k => (3,j,k,false)))
def keys (q : Input) : List KeyID :=
  variableKeys q++clauseKeys q++xorKeys q++connectorKeys q
def record (q : Input) (k : KeyID) : WeightedMatchingInterpolation.SignedEdge :=
  match k.1 with
  | 0 => variableRecord q.val k.2.1 k.2.2.1 k.2.2.2
  | 1 => ((clauseVertex q.val k.2.1 k.2.2.1,
      clauseVertex q.val k.2.1 (if k.2.2.2 then nextSlot q.val k.2.2.1 else k.2.2.1)),
        k.2.2.2 && decide (k.2.2.1=(occurrences q.val).length))
  | 2 => xorRecord q.val k.2.1 (xorLocal.getD k.2.2.1 ((0,0),false))
  | 3 => (connectors q.val k.2.1).getD k.2.2.1 ((0,0),false)
  | _ => ((0,0),false)

private theorem range_getD {A : Type} (xs : List A) (d : A) :
    (List.range xs.length).map (fun i => xs.getD i d)=xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.length_map,List.length_range] at hi
    simpa only [List.getElem_map,List.getElem_range] using (List.getD_eq_getElem xs d hi)

theorem variableKeysBlock_records (q : Input) (v j : ℕ) :
    (variableKeysBlock q v j).map (record q)=variableBlock q.val v j := by
  unfold variableKeysBlock variableBlock
  split <;> split <;> rfl
theorem clauseKeysBlock_records (q : Input) (c j : ℕ) :
    [(1,c,j,false),(1,c,j,true)].map (record q)=clauseBlock q.val c j := rfl
theorem keys_records (q : Input) : (keys q).map (record q)=(raw q.val).2 := by
  have hv : (variableKeys q).map (record q) = variableEdges q.val := by
    unfold variableKeys variableEdges
    try simp only [List.map_flatMap]
    apply congrArg (List.flatMap · (List.range q.val.1))
    funext v
    try simp only [List.map_flatMap]
    apply congrArg (List.flatMap · (List.range (slots q.val)))
    funext j
    exact variableKeysBlock_records q v j
  have hc : (clauseKeys q).map (record q) = clauseEdges q.val := by
    unfold clauseKeys clauseEdges
    try simp only [List.map_flatMap]
    apply congrArg (List.flatMap · (List.range q.val.2.length))
    funext c
    try simp only [List.map_flatMap]
    rfl
  have hx : (xorKeys q).map (record q) = xorEdges q.val := by
    unfold xorKeys xorEdges
    simp only [List.map_flatMap,List.map_map]
    apply congrArg (List.flatMap · (List.range (occurrences q.val).length))
    funext j
    change (List.range xorLocal.length).map
      (fun k => xorRecord q.val j (xorLocal.getD k ((0,0),false)))=xorLocal.map (xorRecord q.val j)
    simpa only [List.map_map,Function.comp_def] using congrArg (List.map (xorRecord q.val j)) (range_getD xorLocal ((0,0),false))
  have ht : (connectorKeys q).map (record q) = connectorEdges q.val := by
    unfold connectorKeys connectorEdges
    simp only [List.map_flatMap,List.map_map]
    apply congrArg (List.flatMap · (List.range (occurrences q.val).length))
    funext j
    change (List.range (connectors q.val j).length).map
      (fun k => (connectors q.val j).getD k ((0,0),false))=connectors q.val j
    exact range_getD _ _
  simp only [keys,raw,List.map_append,hv,hc,hx,ht]

private theorem indexed_nodup (n : ℕ) (f : ℕ → List KeyID) (coord : KeyID → ℕ)
    (hn : ∀ i,i<n → (f i).Nodup) (hc : ∀ i,∀ e∈f i,coord e=i) :
    ((List.range n).flatMap f).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro i hi
    exact hn i (List.mem_range.mp hi)
  · apply (List.nodup_range (n := n)).imp
    intro i j hij e hei hej
    exact hij ((hc i e hei).symm.trans (hc j e hej))

private theorem variableBlock_key_fields (q : Input) (v j : ℕ) (k : KeyID)
    (hk : k∈variableKeysBlock q v j) : k.1=0 ∧ k.2.1=v ∧ k.2.2.1=j := by
  unfold variableKeysBlock at hk
  split at hk <;> split at hk <;> simp_all
  all_goals aesop
private theorem variableBlock_keys_nodup (q : Input) (v j : ℕ) : (variableKeysBlock q v j).Nodup := by
  unfold variableKeysBlock
  split <;> split <;> simp

theorem variableKeys_nodup (q : Input) : (variableKeys q).Nodup := by
  unfold variableKeys
  apply indexed_nodup q.val.1 _ (fun k => k.2.1)
  · intro v _
    exact indexed_nodup (slots q.val) _ (fun k => k.2.2.1)
      (fun j _ => variableBlock_keys_nodup q v j)
      (fun j k hk => (variableBlock_key_fields q v j k hk).2.2)
  · intro v k hk
    obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hk
    exact (variableBlock_key_fields q v j k hj).2.1
theorem clauseKeys_nodup (q : Input) : (clauseKeys q).Nodup := by
  unfold clauseKeys
  apply indexed_nodup q.val.2.length _ (fun k => k.2.1)
  · intro c _
    apply indexed_nodup (slots q.val) _ (fun k => k.2.2.1)
    · intro j _; simp
    · intro j k hk
      simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl <;> rfl
  · intro c k hk
    obtain ⟨j,_,hj⟩ := List.mem_flatMap.mp hk
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hj
    rcases hj with rfl | rfl <;> rfl
theorem xorKeys_nodup (q : Input) : (xorKeys q).Nodup := by
  unfold xorKeys
  apply indexed_nodup (occurrences q.val).length _ (fun k => k.2.1)
  · intro j _
    apply List.nodup_range.map
    intro a b h
    exact congrArg (fun k : KeyID => k.2.2.1) h
  · intro j k hk
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hk
    rfl
theorem connectorKeys_nodup (q : Input) : (connectorKeys q).Nodup := by
  unfold connectorKeys
  apply indexed_nodup (occurrences q.val).length _ (fun k => k.2.1)
  · intro j _
    apply List.nodup_range.map
    intro a b h
    exact congrArg (fun k : KeyID => k.2.2.1) h
  · intro j k hk
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hk
    rfl

theorem variableKeys_tag (q : Input) (k : KeyID) (hk : k∈variableKeys q) : k.1=0 := by
  obtain ⟨v,_,h⟩ := List.mem_flatMap.mp hk
  obtain ⟨j,_,hk⟩ := List.mem_flatMap.mp h
  exact (variableBlock_key_fields q v j k hk).1
theorem clauseKeys_tag (q : Input) (k : KeyID) (hk : k∈clauseKeys q) : k.1=1 := by
  obtain ⟨c,_,h⟩ := List.mem_flatMap.mp hk
  obtain ⟨j,_,h⟩ := List.mem_flatMap.mp h
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl <;> rfl
theorem xorKeys_tag (q : Input) (k : KeyID) (hk : k∈xorKeys q) : k.1=2 := by
  obtain ⟨j,_,h⟩ := List.mem_flatMap.mp hk
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp h
  rfl
theorem connectorKeys_tag (q : Input) (k : KeyID) (hk : k∈connectorKeys q) : k.1=3 := by
  obtain ⟨j,_,h⟩ := List.mem_flatMap.mp hk
  obtain ⟨r,_,rfl⟩ := List.mem_map.mp h
  rfl
theorem keys_nodup (q : Input) : (keys q).Nodup := by
  simp only [keys,List.append_assoc]
  apply List.nodup_append.mpr
  refine ⟨variableKeys_nodup q,?_,?_⟩
  · apply List.nodup_append.mpr
    refine ⟨clauseKeys_nodup q,?_,?_⟩
    · apply List.nodup_append.mpr
      refine ⟨xorKeys_nodup q,connectorKeys_nodup q,?_⟩
      intro k hx l hc heq
      subst l
      have h₂ := xorKeys_tag q k hx
      have h₃ := connectorKeys_tag q k hc
      omega
    · intro k hc l hk heq
      subst l
      have h₁ := clauseKeys_tag q k hc
      rcases List.mem_append.mp hk with hx | ht
      · have h₂ := xorKeys_tag q k hx; omega
      · have h₃ := connectorKeys_tag q k ht; omega
  · intro k hv l hk heq
    subst l
    have h₀ := variableKeys_tag q k hv
    rcases List.mem_append.mp hk with hc | hk
    · have h₁ := clauseKeys_tag q k hc; omega
    · rcases List.mem_append.mp hk with hx | ht
      · have h₂ := xorKeys_tag q k hx; omega
      · have h₃ := connectorKeys_tag q k ht; omega

abbrev Keys (q : Input) := ↥((keys q).toFinset)
def keyIndexEquiv (q : Input) : Keys q ≃ Fin (keys q).length where
  toFun k := ⟨(keys q).idxOf k.val,List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp k.property)⟩
  invFun i := ⟨(keys q).get i,List.mem_toFinset.mpr (List.get_mem _ _)⟩
  left_inv k := by
    apply Subtype.ext
    exact List.getElem_idxOf (List.idxOf_lt_length_iff.mpr (List.mem_toFinset.mp k.property))
  right_inv i := Fin.ext ((keys_nodup q).idxOf_getElem i.val i.isLt)
def edgeEquiv (q : Input) : Keys q ≃ WeightedMatchingInterpolation.OriginalEdges (graph q) :=
  (keyIndexEquiv q).trans (finCongr (by simpa only [graph,List.length_map] using congrArg List.length (keys_records q)))
theorem edgeEquiv_record (q : Input) (k : Keys q) :
    WeightedMatchingInterpolation.originalEdge (graph q) (edgeEquiv q k)=record q k.val := by
  have hm := List.mem_toFinset.mp k.property
  have hi := List.idxOf_lt_length_iff.mpr hm
  have he := congrArg (fun xs : List WeightedMatchingInterpolation.SignedEdge => xs[(keys q).idxOf k.val]?) (keys_records q)
  have hj : (keys q).idxOf k.val < (raw q.val).2.length := by
    have hlen := congrArg List.length (keys_records q)
    simpa only [List.length_map] using hlen ▸ (show (keys q).idxOf k.val < ((keys q).map (record q)).length by simpa using hi)
  rw [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem_idxOf,Option.map_some,List.getElem?_eq_getElem hj] at he
  exact (Option.some.inj he).symm

def keyGraph (q : Input) : FiniteGraph (Fin (vertexCount q.val)) (Keys q) where
  left k := ⟨(actualLeft (graph q) (edgeEquiv q k)).val, by simpa only [graph,raw] using (actualLeft (graph q) (edgeEquiv q k)).isLt⟩
  right k := ⟨(actualRight (graph q) (edgeEquiv q k)).val, by simpa only [graph,raw] using (actualRight (graph q) (edgeEquiv q k)).isLt⟩
  weight k := if (record q k.val).2 then -1 else 1
def keyMatchingEquiv (q : Input) : WeightedMatchingInterpolation.Matching (graph q) ≃ Matching (keyGraph q) where
  toFun m := ⟨fun r => (edgeEquiv q).symm (m.val r),by
    constructor
    · intro r
      apply Fin.ext
      change (WeightedMatchingInterpolation.originalEdge (graph q) (edgeEquiv q ((edgeEquiv q).symm (m.val r)))).1.1=r.val
      simpa only [Equiv.apply_symm_apply] using m.property.1 r
    · intro c
      obtain ⟨r,hr,hu⟩ := m.property.2 c
      refine ⟨r,?_,?_⟩
      · apply Fin.ext
        change (WeightedMatchingInterpolation.originalEdge (graph q) (edgeEquiv q ((edgeEquiv q).symm (m.val r)))).1.2=c.val
        simpa only [Equiv.apply_symm_apply] using hr
      · intro r' hr'
        apply hu
        have h := congrArg Fin.val hr'
        simpa only [keyGraph,actualRight,Equiv.apply_symm_apply] using h⟩
  invFun m := ⟨fun r => edgeEquiv q (m.val r),by
    constructor
    · intro r
      exact congrArg Fin.val (m.property.1 r)
    · intro c
      obtain ⟨r,hr,hu⟩ := m.property.2 c
      refine ⟨r,congrArg Fin.val hr,?_⟩
      intro r' hr'
      apply hu
      exact Fin.ext hr'⟩
  left_inv m := by apply Subtype.ext; funext r; exact Equiv.apply_symm_apply _ _
  right_inv m := by apply Subtype.ext; funext r; exact Equiv.symm_apply_apply _ _
theorem integer_key_selection_sum (q : Input) :
    WeightedMatchingInterpolation.integerValue (graph q)=
      ∑ s : Selection (keyGraph q),selectionWeight (keyGraph q) s := by
  rw [← matching_sum_selection,← (keyMatchingEquiv q).sum_comp (matchingWeight (keyGraph q))]
  unfold WeightedMatchingInterpolation.integerValue
  apply Finset.sum_congr rfl
  intro m _
  change (-1 : ℤ)^WeightedMatchingInterpolation.negativeCount (graph q) m =
    ∏ r : Fin (vertexCount q.val), if (record q ((edgeEquiv q).symm (m.val r)).val).2 then (-1 : ℤ) else 1
  simp_rw [← edgeEquiv_record,Equiv.apply_symm_apply]
  have h (r : Fin (vertexCount q.val)) :
      (if (WeightedMatchingInterpolation.originalEdge (graph q) (m.val r)).2 then (-1 : ℤ) else 1)=
        (-1 : ℤ)^(if (WeightedMatchingInterpolation.originalEdge (graph q) (m.val r)).2 then 1 else 0) := by
    cases hb : (WeightedMatchingInterpolation.originalEdge (graph q) (m.val r)).2 <;> simp [hb]
  simp_rw [h]
  exact (Finset.prod_pow_eq_pow_sum _ _ _).symm

/-- Literal XOR row occupations are connector bits 1/3; column occupations
are 0/2. Full-word transpose equality is derived from the old actual sum,
not from a free symmetry or gate assumption. -/
theorem xor_transpose_ports (a b c d : Bool) :
    ValiantXor.actualTensor ![c,d,a,b]=ValiantXor.actualTensor ![a,b,c,d] := by
  rw [ValiantXor.actual_tensor_exact,ValiantXor.actual_tensor_exact]
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

theorem keys_tags (q : Input) (k : Keys q) :
    k.val.1=0 ∨ k.val.1=1 ∨ k.val.1=2 ∨ k.val.1=3 := by
  have hm := List.mem_toFinset.mp k.property
  simp only [keys,List.mem_append,or_assoc] at hm
  rcases hm with hv | hc | hx | ht
  · exact Or.inl (variableKeys_tag q k.val hv)
  · exact Or.inr (Or.inl (clauseKeys_tag q k.val hc))
  · exact Or.inr (Or.inr (Or.inl (xorKeys_tag q k.val hx)))
  · exact Or.inr (Or.inr (Or.inr (connectorKeys_tag q k.val ht)))
def segmentWeight (q : Input) (s : Selection (keyGraph q)) (tag : ℕ) : ℤ :=
  ∏ k∈s.val,if k.val.1=tag then (keyGraph q).weight k else 1

theorem weight_four_segments (q : Input) (s : Selection (keyGraph q)) :
    selectionWeight (keyGraph q) s=
      segmentWeight q s 0*segmentWeight q s 1*segmentWeight q s 2*segmentWeight q s 3 := by
  unfold selectionWeight segmentWeight
  rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro k _
  rcases keys_tags q k with h | h | h | h <;> simp [h]
theorem variable_edge_unit (q : Input) (k : Keys q) (h : k.val.1=0) : (keyGraph q).weight k=1 := by
  simp [keyGraph,record,h,variableRecord]
theorem connector_edge_unit (q : Input) (k : Keys q) (h : k.val.1=3) : (keyGraph q).weight k=1 := by
  have hm := List.mem_toFinset.mp k.property
  simp only [keys,List.mem_append,or_assoc] at hm
  have hc : k.val∈connectorKeys q := by
    rcases hm with hv | hc | hx | ht
    · have hz := variableKeys_tag q k.val hv; omega
    · have hz := clauseKeys_tag q k.val hc; omega
    · have hz := xorKeys_tag q k.val hx; omega
    · exact ht
  obtain ⟨j,_,hr⟩ := List.mem_flatMap.mp hc
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hr
  have hl : r<4 := List.mem_range.mp hr
  change (if (record q k.val).2 then (-1 : ℤ) else 1)=1
  rw [← he]
  interval_cases r <;> simp [record,connectors]
theorem variable_segment_unit (q : Input) (s : Selection (keyGraph q)) : segmentWeight q s 0=1 := by
  apply Finset.prod_eq_one
  intro k _
  split
  · exact variable_edge_unit q k (by assumption)
  · rfl
theorem connector_segment_unit (q : Input) (s : Selection (keyGraph q)) : segmentWeight q s 3=1 := by
  apply Finset.prod_eq_one
  intro k _
  split
  · exact connector_edge_unit q k (by assumption)
  · rfl
theorem weight_signed_segments (q : Input) (s : Selection (keyGraph q)) :
    selectionWeight (keyGraph q) s=segmentWeight q s 1*segmentWeight q s 2 := by
  rw [weight_four_segments,variable_segment_unit,connector_segment_unit,one_mul,mul_one]
theorem integer_segment_sum (q : Input) :
    WeightedMatchingInterpolation.integerValue (graph q)=
      ∑ s : Selection (keyGraph q),segmentWeight q s 1*segmentWeight q s 2 := by
  rw [integer_key_selection_sum]
  exact Finset.sum_congr rfl (fun s _ => weight_signed_segments q s)

def selectedIDs (q : Input) (s : Selection (keyGraph q)) : Finset KeyID := s.val.image Subtype.val
def coordinate (q : Input) (side : Bool) (k : KeyID) : ℕ :=
  if side then (record q k).1.2 else (record q k).1.1
def rowWord (q : Input) (s : Selection (keyGraph q)) (side : Bool) (r : ℕ) : List Bool :=
  ((keys q).filter (fun k => decide (coordinate q side k=r))).map
    (fun k => decide (k∈selectedIDs q s))
theorem key_left_coordinate (q : Input) (k : Keys q) :
    ((keyGraph q).left k).val=coordinate q false k.val := by
  simp only [keyGraph,actualLeft,coordinate,Bool.false_eq_true,if_false,edgeEquiv_record]
theorem key_right_coordinate (q : Input) (k : Keys q) :
    ((keyGraph q).right k).val=coordinate q true k.val := by
  simp only [keyGraph,actualRight,coordinate,if_true,edgeEquiv_record]

theorem selectedIDs_mem_keys (q : Input) (s : Selection (keyGraph q)) (k : KeyID)
    (hk : k∈selectedIDs q s) : k∈keys q := by
  obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hk
  exact List.mem_toFinset.mp e.property

theorem selectedID_filter (q : Input) (s : Selection (keyGraph q)) (side : Bool)
    (r : Fin (vertexCount q.val)) :
    (selectedIDs q s).filter (fun k => coordinate q side k=r.val)=
      (s.val.filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=r)).image Subtype.val := by
  ext k
  simp only [selectedIDs,Finset.mem_filter,Finset.mem_image]
  constructor
  · rintro ⟨⟨e,he,hk⟩,hc⟩
    refine ⟨e,⟨he,?_⟩,hk⟩
    apply Fin.ext
    cases side
    · simpa only [Bool.false_eq_true,ite_false,ite_true,key_left_coordinate,hk] using hc
    · simpa only [Bool.false_eq_true,ite_false,ite_true,key_right_coordinate,hk] using hc
  · rintro ⟨e,⟨he,hc⟩,hk⟩
    refine ⟨⟨e,he,hk⟩,?_⟩
    have hv := congrArg Fin.val hc
    cases side
    · simpa only [Bool.false_eq_true,ite_false,ite_true,key_left_coordinate,hk] using hv
    · simpa only [Bool.false_eq_true,ite_false,ite_true,key_right_coordinate,hk] using hv

/-- The actual original ordered occurrence word at EVERY row and column.
The proof does not deduplicate endpoint pairs or discard unpaired XOR bits.
-/
theorem rowWord_one (q : Input) (s : Selection (keyGraph q)) (side : Bool)
    (r : Fin (vertexCount q.val)) : (rowWord q s side r.val).count true=1 := by
  let xs := (keys q).filter (fun k => decide (coordinate q side k=r.val))
  let p := fun k : KeyID => decide (k∈selectedIDs q s)
  have hn : (xs.filter p).Nodup := ((keys_nodup q).filter _).filter _
  have hset : (xs.filter p).toFinset=(selectedIDs q s).filter (fun k => coordinate q side k=r.val) := by
    ext k
    simp only [xs,p,List.mem_toFinset,List.mem_filter,Finset.mem_filter,decide_eq_true_eq]
    change ((k∈keys q ∧ coordinate q side k=r.val) ∧ k∈selectedIDs q s) ↔ _
    constructor
    · rintro ⟨⟨_,hc⟩,hs⟩; exact ⟨hs,hc⟩
    · rintro ⟨hs,hc⟩; exact ⟨⟨selectedIDs_mem_keys q s k hs,hc⟩,hs⟩
  have hw : (rowWord q s side r.val).count true=(xs.filter p).length := by
    simp [rowWord,xs,p,List.count,List.countP_map,List.countP_eq_length_filter,List.filter_map,Function.comp_def]
  rw [hw,← List.toFinset_card_of_nodup hn,hset,selectedID_filter,
    Finset.card_image_of_injective _ Subtype.val_injective]
  cases side
  · exact s.property.1 r
  · exact s.property.2 r

/-- Ordered physical incidence words split in exactly the original four
raw segments. All connector/auxiliary occurrences remain in the words. -/
theorem rowWord_four_segments (q : Input) (s : Selection (keyGraph q)) (side : Bool) (r : ℕ) :
    rowWord q s side r=
      ((variableKeys q).filter (fun k => decide (coordinate q side k=r))).map (fun k => decide (k∈selectedIDs q s)) ++
      ((clauseKeys q).filter (fun k => decide (coordinate q side k=r))).map (fun k => decide (k∈selectedIDs q s)) ++
      ((xorKeys q).filter (fun k => decide (coordinate q side k=r))).map (fun k => decide (k∈selectedIDs q s)) ++
      ((connectorKeys q).filter (fun k => decide (coordinate q side k=r))).map (fun k => decide (k∈selectedIDs q s)) := by
  simp only [rowWord,keys,List.filter_append,List.map_append]

theorem variable_key_member (q : Input) (v j : ℕ) (b : Bool) :
    (0,v,j,b)∈keys q ↔ v<q.val.1 ∧ j<slots q.val ∧ isMarked q.val v j b=false := by
  have hnon : (0,v,j,b)∉clauseKeys q ∧ (0,v,j,b)∉xorKeys q ∧ (0,v,j,b)∉connectorKeys q := by
    refine ⟨?_,?_,?_⟩
    · intro h; have ht := clauseKeys_tag q _ h; simp at ht
    · intro h; have ht := xorKeys_tag q _ h; simp at ht
    · intro h; have ht := connectorKeys_tag q _ h; simp at ht
  simp only [keys,List.mem_append,hnon.1,hnon.2.1,hnon.2.2,or_false]
  cases b <;>
    simp [variableKeys,List.mem_flatMap,List.mem_range,variableKeysBlock]

def lookup (q : Input) (s : Selection (keyGraph q)) (k : KeyID) : Bool :=
  decide (k∈selectedIDs q s)
def variableCapture (q : Input) (s : Selection (keyGraph q)) : Source.FamilyChoice q := fun v i =>
  (lookup q s (0,v.val,i.val,false),lookup q s (0,v.val,i.val,true))
def clauseCapture (q : Input) (s : Selection (keyGraph q)) :
    Fin q.val.2.length → Cycle.Choice (occurrences q.val).length := fun c i =>
  (lookup q s (1,c.val,i.val,false),lookup q s (1,c.val,i.val,true))
def variableIncoming (q : Input) (s : Selection (keyGraph q)) : Source.Bits q := fun j => lookup q s (3,j.val,0,false)
def variableOutgoing (q : Input) (s : Selection (keyGraph q)) : Source.Bits q := fun j => lookup q s (3,j.val,1,false)
def clauseIncoming (q : Input) (s : Selection (keyGraph q)) : Source.Bits q := fun j => lookup q s (3,j.val,2,false)
def clauseOutgoing (q : Input) (s : Selection (keyGraph q)) : Source.Bits q := fun j => lookup q s (3,j.val,3,false)
def xorCapture (q : Input) (s : Selection (keyGraph q)) :
    Fin (occurrences q.val).length → Fin xorLocal.length → Bool := fun j k => lookup q s (2,j.val,k.val,false)

theorem deleted_variable_absent (q : Input) (s : Selection (keyGraph q)) (v j : ℕ) (b : Bool)
    (h : isMarked q.val v j b=true) : lookup q s (0,v,j,b)=false := by
  have hn : (0,v,j,b)∉selectedIDs q s := by
    intro hs
    have hm := (variable_key_member q v j b).mp (selectedIDs_mem_keys q s _ hs)
    rw [h] at hm
    exact Bool.noConfusion hm.2.2
  simp [lookup,hn]

/-- The actually absent variable occurrence is forced to zero by key
membership. No deleted edge is supplied for free in the captured family.
-/
theorem variable_capture_erased (q : Input) (s : Selection (keyGraph q)) :
    Source.erase q (variableCapture q s)=variableCapture q s := by
  funext v i
  by_cases hi : i.val<(occurrences q.val).length
  · by_cases hv : (occurrence q.val i.val).2.1=v.val
    · cases hp : (occurrence q.val i.val).2.2
      · have hm : isMarked q.val v.val i.val true=true := by simp [isMarked,hi,hv,hp]
        have hz := deleted_variable_absent q s v.val i.val true hm
        simp [Source.erase,variableCapture,hi,hv,hp,hz]
      · have hm : isMarked q.val v.val i.val false=true := by simp [isMarked,hi,hv,hp]
        have hz := deleted_variable_absent q s v.val i.val false hm
        simp [Source.erase,variableCapture,hi,hv,hp,hz]
    · simp [Source.erase,hi,hv]
  · simp [Source.erase,hi]

/-- Complete literal XOR boundary in its original ordered row0,row1,
column0,column1 convention. No connector or auxiliary port is dropped.
-/
def actualXorWord (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length) : ValiantXor.Word :=
  ![variableOutgoing q s j,clauseOutgoing q s j,variableIncoming q s j,clauseIncoming q s j]
theorem captured_xor_ports (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length) :
    ValiantXor.actualTensor (actualXorWord q s j)=
      ValiantXor.actualTensor ![variableIncoming q s j,clauseIncoming q s j,
        variableOutgoing q s j,clauseOutgoing q s j] := xor_transpose_ports _ _ _ _

theorem slot_code_injective (L a b i j : ℕ) (hi : i<L) (hj : j<L)
    (h : a*L+i=b*L+j) : a=b ∧ i=j := by
  have hab : a=b := by
    by_contra hn
    rcases lt_or_gt_of_ne hn with hab | hba
    · have hm := Nat.mul_le_mul_right L (show a+1≤b by omega)
      nlinarith
    · have hm := Nat.mul_le_mul_right L (show b+1≤a by omega)
      nlinarith
  subst b
  exact ⟨rfl,by omega⟩

private theorem variable_key_spec (q : Input) (k : KeyID) (hk : k∈variableKeys q) :
    ∃ v,v<q.val.1 ∧ ∃ i,i<slots q.val ∧ ∃ b,k=(0,v,i,b) := by
  obtain ⟨v,hv,hi⟩ := List.mem_flatMap.mp hk
  obtain ⟨i,hi,hk⟩ := List.mem_flatMap.mp hi
  refine ⟨v,List.mem_range.mp hv,i,List.mem_range.mp hi,?_⟩
  unfold variableKeysBlock at hk
  rcases List.mem_append.mp hk with hd | hs
  · cases hm : isMarked q.val v i false <;> simp [-finRotate_apply,hm] at hd
    exact ⟨false,hd⟩
  · cases hm : isMarked q.val v i true <;> simp [-finRotate_apply,hm] at hs
    exact ⟨true,hs⟩
private theorem clause_key_spec (q : Input) (k : KeyID) (hk : k∈clauseKeys q) :
    ∃ c,c<q.val.2.length ∧ ∃ i,i<slots q.val ∧ ∃ b,k=(1,c,i,b) := by
  obtain ⟨c,hc,hi⟩ := List.mem_flatMap.mp hk
  obtain ⟨i,hi,hk⟩ := List.mem_flatMap.mp hi
  refine ⟨c,List.mem_range.mp hc,i,List.mem_range.mp hi,?_⟩
  simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hk
  rcases hk with hk | hk
  · exact ⟨false,hk⟩
  · exact ⟨true,hk⟩
private theorem xor_key_spec (q : Input) (k : KeyID) (hk : k∈xorKeys q) :
    ∃ j,j<(occurrences q.val).length ∧ ∃ e,e<xorLocal.length ∧ k=(2,j,e,false) := by
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp hk
  obtain ⟨e,he,hk⟩ := List.mem_map.mp he
  exact ⟨j,List.mem_range.mp hj,e,List.mem_range.mp he,hk.symm⟩
private theorem connector_key_spec (q : Input) (k : KeyID) (hk : k∈connectorKeys q) :
    ∃ j,j<(occurrences q.val).length ∧ ∃ e,e<4 ∧ k=(3,j,e,false) := by
  obtain ⟨j,hj,he⟩ := List.mem_flatMap.mp hk
  obtain ⟨e,he,hk⟩ := List.mem_map.mp he
  exact ⟨j,List.mem_range.mp hj,e,List.mem_range.mp he,hk.symm⟩

theorem variable_node_before_clauses (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val)) :
    variableVertex q.val v.val i.val<q.val.1*slots q.val := by
  have hm := Nat.mul_le_mul_right (slots q.val) (show v.val+1≤q.val.1 by omega)
  dsimp [variableVertex]
  nlinarith [i.isLt]

/-- The complete incoming-row incidence fibre of a variable node. The
only possible connector is literal occurrence i's connector0. Both parallel
cycle occurrences are separate IDs even when their endpoint pairs coincide.
-/
theorem variable_row_key (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val))
    (k : KeyID) (hk : k∈keys q) :
    coordinate q false k=variableVertex q.val v.val i.val ↔
      k=(0,v.val,i.val,false) ∨ k=(0,v.val,i.val,true) ∨
        (i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val ∧ k=(3,i.val,0,false)) := by
  have hvnode := variable_node_before_clauses q v i
  constructor
  · intro he
    have hkeys : k∈variableKeys q ∨ k∈clauseKeys q ∨ k∈xorKeys q ∨ k∈connectorKeys q := by
      simpa only [keys,List.mem_append,or_assoc] using hk
    rcases hkeys with hk | hk | hk | hk
    · obtain ⟨u,hu,j,hj,b,hk⟩ := variable_key_spec q k hk
      have hc : u*slots q.val+j=v.val*slots q.val+i.val := by
        simpa [-finRotate_apply,coordinate,record,hk,variableRecord,variableVertex] using he
      obtain ⟨huv,hji⟩ := slot_code_injective _ u v.val j i.val hj i.isLt hc
      rw [huv,hji] at hk
      cases b
      · exact Or.inl hk
      · exact Or.inr (Or.inl hk)
    · obtain ⟨c,_,j,_,b,hk⟩ := clause_key_spec q k hk
      have hc : q.val.1*slots q.val+c*slots q.val+j=variableVertex q.val v.val i.val := by
        simpa [-finRotate_apply,coordinate,record,hk,clauseVertex] using he
      omega
    · obtain ⟨j,_,e,_,hk⟩ := xor_key_spec q k hk
      have hc : base q.val+4*j+(xorLocal.getD e ((0,0),false)).1.1=variableVertex q.val v.val i.val := by
        simpa [-finRotate_apply,coordinate,record,hk,xorRecord,xorVertex] using he
      have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
      omega
    · obtain ⟨j,hj,e,he',hk⟩ := connector_key_spec q k hk
      interval_cases e
      · have hc : (occurrence q.val j).2.1*slots q.val+j=v.val*slots q.val+i.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,variableVertex] using he
        have hj' : j<slots q.val := by unfold slots; omega
        obtain ⟨huv,hji⟩ := slot_code_injective _ _ _ _ _ hj' i.isLt hc
        subst j
        exact Or.inr (Or.inr ⟨hj,huv,hk⟩)
      · have hc : base q.val+4*j=variableVertex q.val v.val i.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex] using he
        have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
        omega
      · have hc : q.val.1*slots q.val+(occurrence q.val j).1*slots q.val+j=variableVertex q.val v.val i.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,clauseVertex] using he
        omega
      · have hc : base q.val+4*j+1=variableVertex q.val v.val i.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex] using he
        have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
        omega
  · rintro (hk | hk | ⟨hi,hv,hk⟩)
    · simp [-finRotate_apply,coordinate,record,hk,variableRecord]
    · simp [-finRotate_apply,coordinate,record,hk,variableRecord]
    · simp [-finRotate_apply,coordinate,record,hk,connectors,hv]

def variableRowCandidates (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val)) : Finset KeyID :=
  {(0,v.val,i.val,false),(0,v.val,i.val,true)} ∪
    (if i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
      then {(3,i.val,0,false)} else ∅)

theorem variable_row_filter (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    (selectedIDs q s).filter (fun k => coordinate q false k=variableVertex q.val v.val i.val)=
      selectedIDs q s∩variableRowCandidates q v i := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈selectedIDs q s
  · simp only [hs,true_and]
    rw [variable_row_key q v i k (selectedIDs_mem_keys q s k hs)]
    by_cases hc : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
    · simp [-finRotate_apply,variableRowCandidates,hc,← and_assoc]
    · simp [-finRotate_apply,variableRowCandidates,hc,← and_assoc]
  · simp [-finRotate_apply,hs]

theorem variable_row_card (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    (selectedIDs q s∩variableRowCandidates q v i).card=1 := by
  rw [← variable_row_filter]
  let r : Fin (vertexCount q.val) :=
    ⟨variableVertex q.val v.val i.val,variableVertex_lt q.val v.val i.val v.isLt i.isLt⟩
  change ((selectedIDs q s).filter (fun k => coordinate q false k=r.val)).card=1
  rw [selectedID_filter,Finset.card_image_of_injective _ Subtype.val_injective]
  exact s.property.1 r

private theorem capture_intersection_card_sum {A : Type} [DecidableEq A] (s t : Finset A) :
    (s∩t).card=∑k∈t,if k∈s then (1 : ℕ) else 0 := by
  have he : s∩t=t.filter (fun k=>k∈s) := by ext k; simp [and_comm]
  rw [he,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem variable_row_bits (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    Cycle.bit ((variableCapture q s v i).1)+Cycle.bit ((variableCapture q s v i).2)+
      (if i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
        then Cycle.bit (lookup q s (3,i.val,0,false)) else 0)=1 := by
  have hc := variable_row_card q s v i
  rw [capture_intersection_card_sum] at hc
  by_cases he : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
  all_goals
    simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,variableRowCandidates,
      variableCapture,lookup,Cycle.bit,he,Nat.add_assoc] using hc

/-- FIRST actual local validity producer: the incoming-row half of
RemainingValid, derived from the same raw matching and the absent edge.
No row law, layout, or desired validity is passed by the caller. -/
theorem variable_capture_rows (q : Input) (s : Selection (keyGraph q)) :
    ∀ v i,Cycle.bit ((Source.restore q (variableIncoming q s) (variableCapture q s) v i).1)+
      Cycle.bit ((Source.restore q (variableIncoming q s) (variableCapture q s) v i).2)=1 := by
  intro v i
  have hr := variable_row_bits q s v i
  by_cases hi : i.val<(occurrences q.val).length
  · by_cases hv : (occurrence q.val i.val).2.1=v.val
    · cases hp : (occurrence q.val i.val).2.2
      · have hz := deleted_variable_absent q s v.val i.val true (by simp [-finRotate_apply,isMarked,hi,hv,hp])
        simpa [-finRotate_apply,Source.restore,variableCapture,variableIncoming,hi,hv,hp,hz,Cycle.bit] using hr
      · have hz := deleted_variable_absent q s v.val i.val false (by simp [-finRotate_apply,isMarked,hi,hv,hp])
        simpa [-finRotate_apply,Source.restore,variableCapture,variableIncoming,hi,hv,hp,hz,Cycle.bit,Nat.add_comm] using hr
    · simpa [-finRotate_apply,Source.restore,hi,hv] using hr
  · simpa [-finRotate_apply,Source.restore,hi] using hr

theorem nextSlot_injective (q : Input) (i j : ℕ) (hi : i<slots q.val) (hj : j<slots q.val)
    (h : nextSlot q.val i=nextSlot q.val j) : i=j := by
  by_cases hi' : i<(occurrences q.val).length <;>
    by_cases hj' : j<(occurrences q.val).length
  · simpa [-finRotate_apply,nextSlot,hi',hj'] using h
  · have h' : i+1=0 := by simpa [-finRotate_apply,nextSlot,hi',hj'] using h
    omega
  · have h' : 0=j+1 := by simpa [-finRotate_apply,nextSlot,hi',hj'] using h
    omega
  · unfold slots at hi hj
    omega

theorem nextSlot_ne_of_nonempty (q : Input) (i : Fin (slots q.val))
    (hm : 0<(occurrences q.val).length) : nextSlot q.val i.val≠i.val := by
  by_cases hi : i.val<(occurrences q.val).length
  · simp [-finRotate_apply,nextSlot,hi]
  · have hb := i.isLt
    unfold slots at hb
    have he : i.val=(occurrences q.val).length := by omega
    simp [-finRotate_apply,nextSlot,hi,he]; omega

def positiveColumn (q : Input) (v : Fin q.val.1) (t : Fin (slots q.val)) : Prop :=
  t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).2.1=v.val ∧
    (occurrence q.val t.val).2.2=true
def negativeColumn (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val)) : Prop :=
  i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val ∧
    (occurrence q.val i.val).2.2=false
instance (q : Input) (v : Fin q.val.1) (t : Fin (slots q.val)) : Decidable (positiveColumn q v t) := by
  unfold positiveColumn
  infer_instance
instance (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val)) : Decidable (negativeColumn q v i) := by
  unfold negativeColumn
  infer_instance

/-- Complete column fibre at next i. A diagonal connector at next i and
a forward connector at i are independent ORIGINAL literal occurrences.
-/
theorem variable_column_key (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val))
    (k : KeyID) (hk : k∈keys q) :
    coordinate q true k=variableVertex q.val v.val (Cycle.next (occurrences q.val).length i).val ↔
      k=(0,v.val,(Cycle.next (occurrences q.val).length i).val,false) ∨ k=(0,v.val,i.val,true) ∨
      (positiveColumn q v (Cycle.next (occurrences q.val).length i) ∧
        k=(3,(Cycle.next (occurrences q.val).length i).val,1,false)) ∨
      (negativeColumn q v i ∧ k=(3,i.val,1,false)) := by
  let t := Cycle.next (occurrences q.val).length i
  have ht : nextSlot q.val i.val=t.val := nextSlot_rotate q.val i
  have hvnode := variable_node_before_clauses q v t
  constructor
  · intro he
    have hkeys : k∈variableKeys q ∨ k∈clauseKeys q ∨ k∈xorKeys q ∨ k∈connectorKeys q := by
      simpa only [keys,List.mem_append,or_assoc] using hk
    rcases hkeys with hk | hk | hk | hk
    · obtain ⟨u,_,j,hj,b,hk⟩ := variable_key_spec q k hk
      cases b
      · have hc : u*slots q.val+j=v.val*slots q.val+t.val := by
          simpa [-finRotate_apply,coordinate,record,hk,variableRecord,variableVertex,t] using he
        obtain ⟨huv,hjt⟩ := slot_code_injective _ _ _ _ _ hj t.isLt hc
        rw [huv,hjt] at hk
        exact Or.inl hk
      · have hc : u*slots q.val+nextSlot q.val j=v.val*slots q.val+t.val := by
          simpa [-finRotate_apply,coordinate,record,hk,variableRecord,variableVertex,t] using he
        obtain ⟨huv,hjt⟩ := slot_code_injective _ _ _ _ _ (nextSlot_lt q.val j) t.isLt hc
        have hji := nextSlot_injective q j i.val hj i.isLt (hjt.trans ht.symm)
        rw [huv,hji] at hk
        exact Or.inr (Or.inl hk)
    · obtain ⟨c,_,j,_,b,hk⟩ := clause_key_spec q k hk
      have hc : q.val.1*slots q.val+c*slots q.val+
          (if b then nextSlot q.val j else j)=variableVertex q.val v.val t.val := by
        simpa [-finRotate_apply,coordinate,record,hk,clauseVertex,t] using he
      omega
    · obtain ⟨j,_,e,_,hk⟩ := xor_key_spec q k hk
      have hc : base q.val+4*j+(xorLocal.getD e ((0,0),false)).1.2=variableVertex q.val v.val t.val := by
        simpa [-finRotate_apply,coordinate,record,hk,xorRecord,xorVertex,t] using he
      have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
      omega
    · obtain ⟨j,hj,e,he',hk⟩ := connector_key_spec q k hk
      interval_cases e
      · have hc : base q.val+4*j=variableVertex q.val v.val t.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
        have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
        omega
      · cases hp : (occurrence q.val j).2.2
        · have hc : (occurrence q.val j).2.1*slots q.val+nextSlot q.val j=
              v.val*slots q.val+t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,hp,variableVertex,t] using he
          obtain ⟨huv,hjt⟩ := slot_code_injective _ _ _ _ _ (nextSlot_lt q.val j) t.isLt hc
          have hj' : j<slots q.val := by unfold slots; omega
          have hji := nextSlot_injective q j i.val hj' i.isLt (hjt.trans ht.symm)
          subst j
          exact Or.inr (Or.inr (Or.inr ⟨⟨hj,huv,hp⟩,hk⟩))
        · have hc : (occurrence q.val j).2.1*slots q.val+j=v.val*slots q.val+t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,hp,variableVertex,t] using he
          have hj' : j<slots q.val := by unfold slots; omega
          obtain ⟨huv,hjt⟩ := slot_code_injective _ _ _ _ _ hj' t.isLt hc
          subst j
          exact Or.inr (Or.inr (Or.inl ⟨⟨hj,huv,hp⟩,hk⟩))
      · have hc : base q.val+4*j+1=variableVertex q.val v.val t.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
        have hb : q.val.1*slots q.val≤base q.val := by dsimp [base]; nlinarith
        omega
      · have hc : q.val.1*slots q.val+(occurrence q.val j).1*slots q.val+j=
            variableVertex q.val v.val t.val := by
          simpa [-finRotate_apply,coordinate,record,hk,connectors,clauseVertex,t] using he
        omega
  · rintro (hk | hk | ⟨⟨hj,hv,hp⟩,hk⟩ | ⟨⟨hj,hv,hp⟩,hk⟩)
    · simp [-finRotate_apply,coordinate,record,hk,variableRecord,t]
    · simp [-finRotate_apply,coordinate,record,hk,variableRecord,ht,t]
    · simp [-finRotate_apply,coordinate,record,hk,connectors,hv,hp,t]
    · simp [-finRotate_apply,coordinate,record,hk,connectors,hv,hp,ht,t]

def variableColumnCandidates (q : Input) (v : Fin q.val.1) (i : Fin (slots q.val)) : Finset KeyID :=
  let t := Cycle.next (occurrences q.val).length i
  {(0,v.val,t.val,false),(0,v.val,i.val,true)} ∪
    (if positiveColumn q v t then {(3,t.val,1,false)} else ∅) ∪
    (if negativeColumn q v i then {(3,i.val,1,false)} else ∅)

theorem variable_column_filter (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    (selectedIDs q s).filter (fun k => coordinate q true k=
        variableVertex q.val v.val (Cycle.next (occurrences q.val).length i).val)=
      selectedIDs q s∩variableColumnCandidates q v i := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈selectedIDs q s
  · simp only [hs,true_and]
    rw [variable_column_key q v i k (selectedIDs_mem_keys q s k hs)]
    by_cases hp : positiveColumn q v (Cycle.next (occurrences q.val).length i) <;>
      by_cases hn : negativeColumn q v i <;> simp [-finRotate_apply,variableColumnCandidates,hp,hn,or_assoc]
  · simp [-finRotate_apply,hs]

theorem variable_column_card (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    (selectedIDs q s∩variableColumnCandidates q v i).card=1 := by
  rw [← variable_column_filter]
  let t := Cycle.next (occurrences q.val).length i
  let r : Fin (vertexCount q.val) :=
    ⟨variableVertex q.val v.val t.val,variableVertex_lt q.val v.val t.val v.isLt t.isLt⟩
  change ((selectedIDs q s).filter (fun k => coordinate q true k=r.val)).card=1
  rw [selectedID_filter,Finset.card_image_of_injective _ Subtype.val_injective]
  exact s.property.2 r

theorem variable_column_bits (q : Input) (s : Selection (keyGraph q))
    (v : Fin q.val.1) (i : Fin (slots q.val)) :
    let t := Cycle.next (occurrences q.val).length i
    Cycle.bit ((variableCapture q s v t).1)+Cycle.bit ((variableCapture q s v i).2)+
      (if positiveColumn q v t then Cycle.bit (lookup q s (3,t.val,1,false)) else 0)+
      (if negativeColumn q v i then Cycle.bit (lookup q s (3,i.val,1,false)) else 0)=1 := by
  dsimp only
  let t := Cycle.next (occurrences q.val).length i
  change Cycle.bit ((variableCapture q s v t).1)+Cycle.bit ((variableCapture q s v i).2)+
    (if positiveColumn q v t then Cycle.bit (lookup q s (3,t.val,1,false)) else 0)+
    (if negativeColumn q v i then Cycle.bit (lookup q s (3,i.val,1,false)) else 0)=1
  have hc := variable_column_card q s v i
  rw [capture_intersection_card_sum] at hc
  change (∑k∈({(0,v.val,t.val,false),(0,v.val,i.val,true)} ∪
    (if positiveColumn q v t then {(3,t.val,1,false)} else ∅) ∪
    (if negativeColumn q v i then {(3,i.val,1,false)} else ∅)),
      if k∈selectedIDs q s then (1 : ℕ) else 0)=1 at hc
  have hne (hn : negativeColumn q v i) : t.val≠i.val := by
    rw [← nextSlot_rotate q.val i]
    exact nextSlot_ne_of_nonempty q i (by unfold negativeColumn at hn; omega)
  by_cases hp : positiveColumn q v t <;> by_cases hn : negativeColumn q v i
  · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,
      variableCapture,lookup,Cycle.bit,hne hn,Ne.symm (hne hn),Nat.add_assoc] using hc
  · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,
      variableCapture,lookup,Cycle.bit,Nat.add_assoc] using hc
  · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,
      variableCapture,lookup,Cycle.bit,Nat.add_assoc] using hc
  · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,
      variableCapture,lookup,Cycle.bit,Nat.add_assoc] using hc

theorem variable_capture_columns (q : Input) (s : Selection (keyGraph q)) :
    ∀ v i,Cycle.bit ((Source.restore q (variableOutgoing q s) (variableCapture q s) v
        (Cycle.next (occurrences q.val).length i)).1)+
      Cycle.bit ((Source.restore q (variableOutgoing q s) (variableCapture q s) v i).2)=1 := by
  intro v i
  let t := Cycle.next (occurrences q.val).length i
  have hc := variable_column_bits q s v i
  have hd : Cycle.bit ((Source.restore q (variableOutgoing q s) (variableCapture q s) v t).1)=
      Cycle.bit ((variableCapture q s v t).1)+
        (if positiveColumn q v t then Cycle.bit (lookup q s (3,t.val,1,false)) else 0) := by
    by_cases hi : t.val<(occurrences q.val).length <;>
      by_cases hv : (occurrence q.val t.val).2.1=v.val <;>
      cases hp : (occurrence q.val t.val).2.2
    all_goals simp [-finRotate_apply,Source.restore,positiveColumn,hi,hv,hp,variableCapture,variableOutgoing]
    have hz := deleted_variable_absent q s v.val t.val false (by simp [-finRotate_apply,isMarked,hi,hv,hp])
    simp [-finRotate_apply,hz,Cycle.bit]
  have hs : Cycle.bit ((Source.restore q (variableOutgoing q s) (variableCapture q s) v i).2)=
      Cycle.bit ((variableCapture q s v i).2)+
        (if negativeColumn q v i then Cycle.bit (lookup q s (3,i.val,1,false)) else 0) := by
    by_cases hi : i.val<(occurrences q.val).length <;>
      by_cases hv : (occurrence q.val i.val).2.1=v.val <;>
      cases hp : (occurrence q.val i.val).2.2
    all_goals simp [-finRotate_apply,Source.restore,negativeColumn,hi,hv,hp,variableCapture,variableOutgoing]
    have hz := deleted_variable_absent q s v.val i.val true (by simp [-finRotate_apply,isMarked,hi,hv,hp])
    simp [-finRotate_apply,hz,Cycle.bit]
  change Cycle.bit ((variableCapture q s v t).1)+Cycle.bit ((variableCapture q s v i).2)+
    (if positiveColumn q v t then Cycle.bit (lookup q s (3,t.val,1,false)) else 0)+
    (if negativeColumn q v i then Cycle.bit (lookup q s (3,i.val,1,false)) else 0)=1 at hc
  rw [hd,hs]
  omega

/-- Complete actual remaining-variable matching, internally produced from
the original raw graph selection. Erasure and BOTH exact-one halves hold.
-/
theorem variable_capture_valid (q : Input) (s : Selection (keyGraph q)) :
    Source.RemainingValid q (variableIncoming q s) (variableOutgoing q s) (variableCapture q s) :=
  ⟨variable_capture_erased q s,variable_capture_rows q s,variable_capture_columns q s⟩
def remainingCapture (q : Input) (s : Selection (keyGraph q)) :
    Source.RemainingMatching q (variableIncoming q s) (variableOutgoing q s) :=
  ⟨variableCapture q s,variable_capture_valid q s⟩

theorem clause_node_before_xors (q : Input) (c : Fin q.val.2.length) (i : Fin (slots q.val)) :
    clauseVertex q.val c.val i.val<base q.val := by
  have hm := Nat.mul_le_mul_right (slots q.val) (show c.val+1≤q.val.2.length by omega)
  dsimp [clauseVertex,base]
  nlinarith [i.isLt]

/-- Complete incidence fibre on either side of a clause cycle. Incoming
uses slot i/connector2; outgoing uses next i/connector3. -/
theorem clause_key_fibre (q : Input) (c : Fin q.val.2.length) (i : Fin (slots q.val))
    (side : Bool) (k : KeyID) (hk : k∈keys q) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    coordinate q side k=clauseVertex q.val c.val t.val ↔
      k=(1,c.val,t.val,false) ∨ k=(1,c.val,i.val,true) ∨
      (t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val ∧
        k=(3,t.val,(if side then 3 else 2),false)) := by
  let t := if side then Cycle.next (occurrences q.val).length i else i
  have ht : (if side then nextSlot q.val i.val else i.val)=t.val := by
    cases side
    · rfl
    · exact nextSlot_rotate q.val i
  have htarget : q.val.1*slots q.val≤clauseVertex q.val c.val t.val := by dsimp [clauseVertex]; omega
  have htarget' := clause_node_before_xors q c t
  constructor
  · intro he
    have hkeys : k∈variableKeys q ∨ k∈clauseKeys q ∨ k∈xorKeys q ∨ k∈connectorKeys q := by
      simpa only [keys,List.mem_append,or_assoc] using hk
    rcases hkeys with hk | hk | hk | hk
    · obtain ⟨u,hu,j,hj,b,hk⟩ := variable_key_spec q k hk
      let a := if side && b then nextSlot q.val j else j
      have ha : a<slots q.val := by
        cases side <;> cases b
        · exact hj
        · exact hj
        · exact hj
        · exact nextSlot_lt q.val j
      have hbefore := variable_node_before_clauses q ⟨u,hu⟩ ⟨a,ha⟩
      change variableVertex q.val u a<q.val.1*slots q.val at hbefore
      have hc : variableVertex q.val u a=clauseVertex q.val c.val t.val := by
        cases side <;> cases b <;> simpa [-finRotate_apply,coordinate,record,hk,variableRecord,a,t] using he
      omega
    · obtain ⟨d,_,j,hj,b,hk⟩ := clause_key_spec q k hk
      cases side
      · have hc : d*slots q.val+j=c.val*slots q.val+i.val := by
          simpa [-finRotate_apply,coordinate,record,hk,clauseVertex,t,Nat.add_assoc] using he
        obtain ⟨hdc,hji⟩ := slot_code_injective _ _ _ _ _ hj i.isLt hc
        rw [hdc,hji] at hk
        cases b
        · exact Or.inl hk
        · exact Or.inr (Or.inl hk)
      · cases b
        · have hc : d*slots q.val+j=c.val*slots q.val+t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,clauseVertex,t,Nat.add_assoc] using he
          obtain ⟨hdc,hjt⟩ := slot_code_injective _ _ _ _ _ hj t.isLt hc
          rw [hdc,hjt] at hk
          exact Or.inl hk
        · have hc : d*slots q.val+nextSlot q.val j=c.val*slots q.val+t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,clauseVertex,t,Nat.add_assoc] using he
          obtain ⟨hdc,hjt⟩ := slot_code_injective _ _ _ _ _ (nextSlot_lt q.val j) t.isLt hc
          have hji := nextSlot_injective q j i.val hj i.isLt (hjt.trans (by simpa using ht.symm))
          rw [hdc,hji] at hk
          exact Or.inr (Or.inl hk)
    · obtain ⟨j,_,e,_,hk⟩ := xor_key_spec q k hk
      have hc : base q.val+4*j+(if side then (xorLocal.getD e ((0,0),false)).1.2
          else (xorLocal.getD e ((0,0),false)).1.1)=clauseVertex q.val c.val t.val := by
        cases side <;> simpa [-finRotate_apply,coordinate,record,hk,xorRecord,xorVertex,t] using he
      omega
    · obtain ⟨j,hj,e,he',hk⟩ := connector_key_spec q k hk
      have hj' : j<slots q.val := by unfold slots; omega
      have hv := occurrence_variable q.val q.property j hj
      have hvnode := variable_node_before_clauses q ⟨(occurrence q.val j).2.1,hv⟩ ⟨j,hj'⟩
      change variableVertex q.val (occurrence q.val j).2.1 j<q.val.1*slots q.val at hvnode
      have hvnext := variable_node_before_clauses q ⟨(occurrence q.val j).2.1,hv⟩
        ⟨nextSlot q.val j,nextSlot_lt q.val j⟩
      change variableVertex q.val (occurrence q.val j).2.1 (nextSlot q.val j)<q.val.1*slots q.val at hvnext
      cases side
      · interval_cases e
        · have hc : variableVertex q.val (occurrence q.val j).2.1 j=clauseVertex q.val c.val t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,t] using he
          omega
        · have hc : base q.val+4*j=clauseVertex q.val c.val t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
          omega
        · have hc : (occurrence q.val j).1*slots q.val+j=c.val*slots q.val+i.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,clauseVertex,t,Nat.add_assoc] using he
          obtain ⟨hcc,hji⟩ := slot_code_injective _ _ _ _ _ hj' i.isLt hc
          subst j
          exact Or.inr (Or.inr ⟨hj,hcc,hk⟩)
        · have hc : base q.val+4*j+1=clauseVertex q.val c.val t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
          omega
      · interval_cases e
        · have hc : base q.val+4*j=clauseVertex q.val c.val t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
          omega
        · cases hp : (occurrence q.val j).2.2
          · have hc : variableVertex q.val (occurrence q.val j).2.1 (nextSlot q.val j)=clauseVertex q.val c.val t.val := by
              simpa [-finRotate_apply,coordinate,record,hk,connectors,hp,t] using he
            omega
          · have hc : variableVertex q.val (occurrence q.val j).2.1 j=clauseVertex q.val c.val t.val := by
              simpa [-finRotate_apply,coordinate,record,hk,connectors,hp,t] using he
            omega
        · have hc : base q.val+4*j+1=clauseVertex q.val c.val t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,t] using he
          omega
        · have hc : (occurrence q.val j).1*slots q.val+j=c.val*slots q.val+t.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,clauseVertex,t,Nat.add_assoc] using he
          obtain ⟨hcc,hjt⟩ := slot_code_injective _ _ _ _ _ hj' t.isLt hc
          subst j
          exact Or.inr (Or.inr ⟨hj,hcc,hk⟩)
  · rintro (hk | hk | ⟨hj,hc,hk⟩)
    · cases side <;> simp [-finRotate_apply,coordinate,record,hk,clauseVertex,t]
    · cases side <;> simp_all [-finRotate_apply,coordinate,record,hk,clauseVertex,t,nextSlot_rotate]
    · cases side <;> simp_all [-finRotate_apply,coordinate,record,hk,connectors,t]

def clauseCandidates (q : Input) (c : Fin q.val.2.length) (i : Fin (slots q.val)) (side : Bool) : Finset KeyID :=
  let t := if side then Cycle.next (occurrences q.val).length i else i
  {(1,c.val,t.val,false),(1,c.val,i.val,true)} ∪
    (if t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val
      then {(3,t.val,(if side then 3 else 2),false)} else ∅)

theorem clause_filter (q : Input) (s : Selection (keyGraph q)) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    (selectedIDs q s).filter (fun k => coordinate q side k=clauseVertex q.val c.val t.val)=
      selectedIDs q s∩clauseCandidates q c i side := by
  let t := if side then Cycle.next (occurrences q.val).length i else i
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈selectedIDs q s
  · simp only [hs,true_and]
    have hcf := clause_key_fibre q c i side k (selectedIDs_mem_keys q s k hs)
    dsimp only at hcf
    rw [hcf]
    by_cases hc : t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val <;>
      simp [-finRotate_apply,clauseCandidates,t,hc,← and_assoc]
  · simp [-finRotate_apply,hs]

theorem clause_card (q : Input) (s : Selection (keyGraph q)) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    (selectedIDs q s∩clauseCandidates q c i side).card=1 := by
  rw [← clause_filter q s c i side]
  let t := if side then Cycle.next (occurrences q.val).length i else i
  let r : Fin (vertexCount q.val) := ⟨clauseVertex q.val c.val t.val,
    clauseVertex_lt q.val c.val t.val c.isLt t.isLt⟩
  change ((selectedIDs q s).filter (fun k => coordinate q side k=r.val)).card=1
  rw [selectedID_filter,Finset.card_image_of_injective _ Subtype.val_injective]
  cases side
  · exact s.property.1 r
  · exact s.property.2 r

theorem clause_bits (q : Input) (s : Selection (keyGraph q)) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    Cycle.bit ((clauseCapture q s c t).1)+Cycle.bit ((clauseCapture q s c i).2)+
      Cycle.bit (Source.boundary q c.val (if side then clauseOutgoing q s else clauseIncoming q s) t)=1 := by
  dsimp only
  let t := if side then Cycle.next (occurrences q.val).length i else i
  change Cycle.bit ((clauseCapture q s c t).1)+Cycle.bit ((clauseCapture q s c i).2)+
    Cycle.bit (Source.boundary q c.val (if side then clauseOutgoing q s else clauseIncoming q s) t)=1
  have hc := clause_card q s c i side
  rw [capture_intersection_card_sum] at hc
  change (∑k∈({(1,c.val,t.val,false),(1,c.val,i.val,true)} ∪
    (if t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val
      then {(3,t.val,(if side then 3 else 2),false)} else ∅)),
        if k∈selectedIDs q s then (1 : ℕ) else 0)=1 at hc
  have ha (h : t.val<(occurrences q.val).length) :
      (if side then clauseOutgoing q s else clauseIncoming q s) ⟨t.val,h⟩=
        lookup q s (3,t.val,(if side then 3 else 2),false) := by
    cases side <;> rfl
  by_cases hi : t.val<(occurrences q.val).length
  · by_cases he : (occurrence q.val t.val).1=c.val
    · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hi,he,ha hi,
        clauseCapture,lookup,Source.boundary,Cycle.bit,Nat.add_assoc] using hc
    · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hi,he,
        clauseCapture,lookup,Source.boundary,Cycle.bit,Nat.add_assoc] using hc
  · simpa [-finRotate_apply,-Finset.sum_boole,-Finset.sum_ite_mem,hi,
      clauseCapture,lookup,Source.boundary,Cycle.bit,Nat.add_assoc] using hc

/-- BOTH sides of the actual clause cycle, with its original fixed dummy
slot and all occurrence connectors. No clause correctness law is input. -/
theorem clause_capture_valid (q : Input) (s : Selection (keyGraph q)) (c : Fin q.val.2.length) :
    Cycle.Valid (Source.boundary q c.val (clauseIncoming q s))
      (Source.boundary q c.val (clauseOutgoing q s)) (clauseCapture q s c) := by
  constructor
  · intro i
    exact clause_bits q s c i false
  · intro i
    exact clause_bits q s c i true
def clauseMatchingCapture (q : Input) (s : Selection (keyGraph q)) (c : Fin q.val.2.length) :
    Cycle.Matching (Source.boundary q c.val (clauseIncoming q s))
      (Source.boundary q c.val (clauseOutgoing q s)) :=
  ⟨clauseCapture q s c,clause_capture_valid q s c⟩


/-- Internal indices refer to the original ten ordered XOR records. They
are not endpoint-pair IDs for the ambient multigraph. -/
abbrev XorIndex := Fin xorLocal.length
def localEdge (e : XorIndex) : ValiantXor.Edge :=
  ValiantXor.activeEdges.get ⟨e.val,by simpa [-finRotate_apply,xorLocal] using e.isLt⟩
def localCoordinate (side : Bool) (e : XorIndex) : ValiantXor.Vertex :=
  if side then (localEdge e).2 else (localEdge e).1

theorem local_edge_coordinates (e : XorIndex) :
    (xorLocal.getD e.val ((0,0),false)).1=((localEdge e).1.val,(localEdge e).2.val) := by
  rw [List.getD_eq_getElem _ _ e.isLt]
  simp only [xorLocal,List.getElem_map,localEdge,List.get_eq_getElem]
theorem local_edge_active (e : XorIndex) : localEdge e∈ValiantXor.template.edges :=
  List.get_mem _ _
theorem local_record_weight (q : Input) (j : Fin (occurrences q.val).length) (e : XorIndex) :
    (if (record q (2,j.val,e.val,false)).2 then (-1 : ℤ) else 1)=
      ValiantXor.matrix (localEdge e).1 (localEdge e).2 := by
  change (if (xorRecord q.val j.val (xorLocal.getD e.val ((0,0),false))).2 then (-1 : ℤ) else 1)=_
  rw [List.getD_eq_getElem _ _ e.isLt]
  simpa only [xorLocal,List.getElem_map,localEdge,List.get_eq_getElem] using
    xorRecord_active_weight q.val j.val (localEdge e) (local_edge_active e)
theorem xor_key_member (q : Input) (j : Fin (occurrences q.val).length) (e : XorIndex) :
    (2,j.val,e.val,false)∈keys q := by
  have hkeys : (2,j.val,e.val,false)∈variableKeys q ∨
      (2,j.val,e.val,false)∈clauseKeys q ∨ (2,j.val,e.val,false)∈xorKeys q ∨
      (2,j.val,e.val,false)∈connectorKeys q := by
    right; right; left
    exact List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,
      List.mem_map.mpr ⟨e.val,List.mem_range.mpr e.isLt,rfl⟩⟩
  simpa only [keys,List.mem_append,or_assoc] using hkeys

def xorConnectorID {q : Input} (j : Fin (occurrences q.val).length) (side : Bool)
    (r : ValiantXor.Vertex) : KeyID := (3,j.val,(if side then 2*r.val else 2*r.val+1),false)

/-- Complete incidence fibre of an XOR vertex: the original internal
records and exactly its original external connector at ports zero/one.
All four boundary bits, including unbalanced words, remain represented. -/
theorem xor_key_fibre (q : Input) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) (k : KeyID) (hk : k∈keys q) :
    coordinate q side k=xorVertex q.val j.val r.val ↔
      (∃ e : XorIndex,k=(2,j.val,e.val,false) ∧ localCoordinate side e=r) ∨
      (r.val<2 ∧ k=xorConnectorID j side r) := by
  have htarget : base q.val≤xorVertex q.val j.val r.val := by dsimp [xorVertex]; omega
  constructor
  · intro he
    have hkeys : k∈variableKeys q ∨ k∈clauseKeys q ∨ k∈xorKeys q ∨ k∈connectorKeys q := by
      simpa only [keys,List.mem_append,or_assoc] using hk
    rcases hkeys with hk | hk | hk | hk
    · obtain ⟨v,hv,i,hi,b,hk⟩ := variable_key_spec q k hk
      let a := if side && b then nextSlot q.val i else i
      have ha : a<slots q.val := by
        cases side <;> cases b
        · exact hi
        · exact hi
        · exact hi
        · exact nextSlot_lt q.val i
      have hp := variable_node_before_clauses q ⟨v,hv⟩ ⟨a,ha⟩
      change variableVertex q.val v a<q.val.1*slots q.val at hp
      have hb : q.val.1*slots q.val≤base q.val := by simp [-finRotate_apply,base,Nat.add_mul]
      have hc : variableVertex q.val v a=xorVertex q.val j.val r.val := by
        cases side <;> cases b <;> simpa [-finRotate_apply,coordinate,record,hk,variableRecord,a] using he
      omega
    · obtain ⟨c,hc,i,hi,b,hk⟩ := clause_key_spec q k hk
      let a := if side && b then nextSlot q.val i else i
      have ha : a<slots q.val := by
        cases side <;> cases b
        · exact hi
        · exact hi
        · exact hi
        · exact nextSlot_lt q.val i
      have hp := clause_node_before_xors q ⟨c,hc⟩ ⟨a,ha⟩
      change clauseVertex q.val c a<base q.val at hp
      have hn : clauseVertex q.val c a=xorVertex q.val j.val r.val := by
        cases side <;> cases b <;> simpa [-finRotate_apply,coordinate,record,hk,a] using he
      omega
    · obtain ⟨a,_,e,he',hk⟩ := xor_key_spec q k hk
      let e' : XorIndex := ⟨e,he'⟩
      have hcoords : (xorLocal.getD e ((0,0),false)).1=
          ((localEdge e').1.val,(localEdge e').2.val) := local_edge_coordinates e'
      rw [hk] at he
      have hc : a*4+(localCoordinate side e').val=j.val*4+r.val := by
        cases side
        · change base q.val+4*a+(xorLocal.getD e ((0,0),false)).1.1=
            base q.val+4*j.val+r.val at he
          rw [hcoords] at he
          simpa [-finRotate_apply,localCoordinate,Nat.mul_comm,Nat.add_assoc] using he
        · change base q.val+4*a+(xorLocal.getD e ((0,0),false)).1.2=
            base q.val+4*j.val+r.val at he
          rw [hcoords] at he
          simpa [-finRotate_apply,localCoordinate,Nat.mul_comm,Nat.add_assoc] using he
      obtain ⟨haj,her⟩ := slot_code_injective 4 a j.val _ _ (localCoordinate side e').isLt r.isLt hc
      refine Or.inl ⟨e',?_,Fin.ext her⟩
      simpa [-finRotate_apply,e',haj] using hk
    · obtain ⟨a,ha,e,he',hk⟩ := connector_key_spec q k hk
      have ha' : a<slots q.val := by unfold slots; omega
      have hv := occurrence_variable q.val q.property a ha
      have hc := occurrence_clause q.val a ha
      have hvd := variable_node_before_clauses q ⟨(occurrence q.val a).2.1,hv⟩ ⟨a,ha'⟩
      change variableVertex q.val (occurrence q.val a).2.1 a<q.val.1*slots q.val at hvd
      have hvs := variable_node_before_clauses q ⟨(occurrence q.val a).2.1,hv⟩
        ⟨nextSlot q.val a,nextSlot_lt q.val a⟩
      change variableVertex q.val (occurrence q.val a).2.1 (nextSlot q.val a)<q.val.1*slots q.val at hvs
      have hcd := clause_node_before_xors q ⟨(occurrence q.val a).1,hc⟩ ⟨a,ha'⟩
      change clauseVertex q.val (occurrence q.val a).1 a<base q.val at hcd
      have hb : q.val.1*slots q.val≤base q.val := by simp [-finRotate_apply,base,Nat.add_mul]
      cases side
      · interval_cases e
        · have hn : variableVertex q.val (occurrence q.val a).2.1 a=xorVertex q.val j.val r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors] using he
          omega
        · have hn : a*4+0=j.val*4+r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,Nat.mul_comm,Nat.add_assoc] using he
          obtain ⟨haj,hr⟩ := slot_code_injective 4 a j.val 0 r.val (by omega) r.isLt hn
          exact Or.inr ⟨by omega,by simpa [-finRotate_apply,xorConnectorID,haj,← hr] using hk⟩
        · have hn : clauseVertex q.val (occurrence q.val a).1 a=xorVertex q.val j.val r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors] using he
          omega
        · have hn : a*4+1=j.val*4+r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,Nat.mul_comm,Nat.add_assoc] using he
          obtain ⟨haj,hr⟩ := slot_code_injective 4 a j.val 1 r.val (by omega) r.isLt hn
          exact Or.inr ⟨by omega,by simpa [-finRotate_apply,xorConnectorID,haj,← hr] using hk⟩
      · interval_cases e
        · have hn : a*4+0=j.val*4+r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,Nat.mul_comm,Nat.add_assoc] using he
          obtain ⟨haj,hr⟩ := slot_code_injective 4 a j.val 0 r.val (by omega) r.isLt hn
          exact Or.inr ⟨by omega,by simpa [-finRotate_apply,xorConnectorID,haj,← hr] using hk⟩
        · cases hp : (occurrence q.val a).2.2
          · have hn : variableVertex q.val (occurrence q.val a).2.1 (nextSlot q.val a)=xorVertex q.val j.val r.val := by
              simpa [-finRotate_apply,coordinate,record,hk,connectors,hp] using he
            omega
          · have hn : variableVertex q.val (occurrence q.val a).2.1 a=xorVertex q.val j.val r.val := by
              simpa [-finRotate_apply,coordinate,record,hk,connectors,hp] using he
            omega
        · have hn : a*4+1=j.val*4+r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors,xorVertex,Nat.mul_comm,Nat.add_assoc] using he
          obtain ⟨haj,hr⟩ := slot_code_injective 4 a j.val 1 r.val (by omega) r.isLt hn
          exact Or.inr ⟨by omega,by simpa [-finRotate_apply,xorConnectorID,haj,← hr] using hk⟩
        · have hn : clauseVertex q.val (occurrence q.val a).1 a=xorVertex q.val j.val r.val := by
            simpa [-finRotate_apply,coordinate,record,hk,connectors] using he
          omega
  · rintro (⟨e,hk,hr⟩ | ⟨hr,hk⟩)
    · subst k
      have hc := local_edge_coordinates e
      cases side
      · change base q.val+4*j.val+(xorLocal.getD e.val ((0,0),false)).1.1=
          base q.val+4*j.val+r.val
        rw [hc]
        exact congrArg (fun n=>base q.val+4*j.val+n) (congrArg Fin.val hr)
      · change base q.val+4*j.val+(xorLocal.getD e.val ((0,0),false)).1.2=
          base q.val+4*j.val+r.val
        rw [hc]
        exact congrArg (fun n=>base q.val+4*j.val+n) (congrArg Fin.val hr)
    · fin_cases r <;> cases side <;> simp [-finRotate_apply,coordinate,record,hk,xorConnectorID,connectors] at *

def xorSelected (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length) :
    Finset XorIndex := Finset.univ.filter (fun e => lookup q s (2,j.val,e.val,false)=true)
def xorFibre (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) : Finset XorIndex :=
  (xorSelected q s j).filter (fun e => localCoordinate side e=r)
def xorBoundary (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) : Bool :=
  if side then ValiantXor.columnOccupied (actualXorWord q s j) r
    else ValiantXor.rowOccupied (actualXorWord q s j) r

theorem xor_boundary_lookup (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    xorBoundary q s j side r=
      if r.val<2 then lookup q s (xorConnectorID j side r) else false := by
  fin_cases r <;> cases side <;>
    simp [-finRotate_apply,xorBoundary,actualXorWord,ValiantXor.rowOccupied,ValiantXor.columnOccupied,
      xorConnectorID,variableIncoming,variableOutgoing,clauseIncoming,clauseOutgoing]

theorem xor_filter (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (selectedIDs q s).filter (fun k => coordinate q side k=xorVertex q.val j.val r.val)=
      ((xorFibre q s j side r).image (fun e => (2,j.val,e.val,false))) ∪
        (if r.val<2 ∧ lookup q s (xorConnectorID j side r)=true
          then {xorConnectorID j side r} else ∅) := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro ⟨hs,hcoord⟩
    rcases (xor_key_fibre q j side r k (selectedIDs_mem_keys q s k hs)).mp hcoord with h | h
    · obtain ⟨e,hk,he⟩ := h
      left
      refine ⟨e,?_,hk.symm⟩
      rw [hk] at hs
      simp [-finRotate_apply,xorFibre,xorSelected,lookup,hs,he]
    · obtain ⟨hr,hk⟩ := h
      right
      rw [hk] at hs
      simp [-finRotate_apply,hr,hk,lookup,hs]
  · rintro (⟨e,he,hk⟩ | hc)
    · have he' := Finset.mem_filter.mp he
      have hs : k∈selectedIDs q s := by
        have h := (Finset.mem_filter.mp he'.1).2
        simpa [-finRotate_apply,lookup,hk] using h
      exact ⟨hs,(xor_key_fibre q j side r k (selectedIDs_mem_keys q s k hs)).mpr
        (Or.inl ⟨e,hk.symm,he'.2⟩)⟩
    · split_ifs at hc with h
      · obtain ⟨hr,hs⟩ := h
        have hk : k=xorConnectorID j side r := by simpa using hc
        have hs' : k∈selectedIDs q s := by simpa [-finRotate_apply,lookup,hk] using hs
        exact ⟨hs',(xor_key_fibre q j side r k (selectedIDs_mem_keys q s k hs')).mpr (Or.inr ⟨hr,hk⟩)⟩
      · simp at hc

/-- Exact-one on EVERY internal XOR row and column, with its actual four
external connector occupations. This is before any signed cancellation. -/
theorem xor_incidence_card (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (xorFibre q s j side r).card+ValiantXor.bitNat (xorBoundary q s j side r)=1 := by
  let v : Fin (vertexCount q.val) := ⟨xorVertex q.val j.val r.val,
    xorVertex_lt q.val j.val r.val j.isLt r.isLt⟩
  have hone : ((selectedIDs q s).filter (fun k => coordinate q side k=v.val)).card=1 := by
    rw [selectedID_filter,Finset.card_image_of_injective _ Subtype.val_injective]
    cases side
    · exact s.property.1 v
    · exact s.property.2 v
  change ((selectedIDs q s).filter (fun k => coordinate q side k=xorVertex q.val j.val r.val)).card=1 at hone
  rw [xor_filter] at hone
  have hd : Disjoint
      ((xorFibre q s j side r).image (fun e => (2,j.val,e.val,false)))
      (if r.val<2 ∧ lookup q s (xorConnectorID j side r)=true
        then {xorConnectorID j side r} else ∅) := by
    apply Finset.disjoint_left.mpr
    intro k hk hc
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hk
    split_ifs at hc <;> simp [-finRotate_apply,xorConnectorID] at hc
  have hinj : Function.Injective (fun e : XorIndex => (2,j.val,e.val,false)) := by
    intro a b h
    exact Fin.ext (congrArg (fun k : KeyID => k.2.2.1) h)
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hinj] at hone
  rw [xor_boundary_lookup]
  by_cases hr : r.val<2 <;> cases hb : lookup q s (xorConnectorID j side r) <;>
    simpa [-finRotate_apply,hr,hb,ValiantXor.bitNat] using hone


private theorem xor_indices_complete (r : ValiantXor.Vertex) : r∈ValiantXor.indices := by
  fin_cases r <;> decide

theorem xor_rows_mem (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : ValiantXor.Vertex) :
    r∈ValiantXor.rows (actualXorWord q s j) ↔
      ValiantXor.rowOccupied (actualXorWord q s j) r=false := by
  simp [ValiantXor.rows,xor_indices_complete r]

theorem xor_row_card (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : ValiantXor.Vertex) (hr : r∈ValiantXor.rows (actualXorWord q s j)) :
    (xorFibre q s j false r).card=1 := by
  have ho := (xor_rows_mem q s j r).mp hr
  simpa [xorBoundary,ho,ValiantXor.bitNat] using xor_incidence_card q s j false r

theorem xor_row_witness (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : ValiantXor.Vertex) (hr : r∈ValiantXor.rows (actualXorWord q s j)) :
    ∃ e : XorIndex,e∈xorSelected q s j ∧ (localEdge e).1=r := by
  obtain ⟨e,he⟩ := Finset.card_pos.mp (show 0<(xorFibre q s j false r).card by
    rw [xor_row_card q s j r hr]; omega)
  exact ⟨e,(Finset.mem_filter.mp he).1,(Finset.mem_filter.mp he).2⟩

/-- The actual selected internal edge of an available XOR row is unique,
not an arbitrary local completion supplied by the caller. -/
def xorRowIndex (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : {r : ValiantXor.Vertex // r∈ValiantXor.rows (actualXorWord q s j)}) : XorIndex :=
  Classical.choose (xor_row_witness q s j r.val r.property)
theorem xor_row_index_mem (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : {r : ValiantXor.Vertex // r∈ValiantXor.rows (actualXorWord q s j)}) :
    xorRowIndex q s j r∈xorSelected q s j :=
  (Classical.choose_spec (xor_row_witness q s j r.val r.property)).1
theorem xor_row_index_row (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : {r : ValiantXor.Vertex // r∈ValiantXor.rows (actualXorWord q s j)}) :
    (localEdge (xorRowIndex q s j r)).1=r.val :=
  (Classical.choose_spec (xor_row_witness q s j r.val r.property)).2

theorem xor_row_unique (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length)
    (r : ValiantXor.Vertex) (hr : r∈ValiantXor.rows (actualXorWord q s j))
    (a b : XorIndex) (ha : a∈xorSelected q s j) (hb : b∈xorSelected q s j)
    (har : (localEdge a).1=r) (hbr : (localEdge b).1=r) : a=b := by
  obtain ⟨e,he⟩ := Finset.card_eq_one.mp (xor_row_card q s j r hr)
  have ha' : a∈xorFibre q s j false r := Finset.mem_filter.mpr ⟨ha,har⟩
  have hb' : b∈xorFibre q s j false r := Finset.mem_filter.mpr ⟨hb,hbr⟩
  rw [he] at ha' hb'
  exact (Finset.mem_singleton.mp ha').trans (Finset.mem_singleton.mp hb').symm

theorem xor_selected_row_available (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) (e : XorIndex) (he : e∈xorSelected q s j) :
    (localEdge e).1∈ValiantXor.rows (actualXorWord q s j) := by
  let r := (localEdge e).1
  have hf : e∈xorFibre q s j false r := Finset.mem_filter.mpr ⟨he,rfl⟩
  have hp := Finset.card_pos.mpr ⟨e,hf⟩
  have hone := xor_incidence_card q s j false r
  apply (xor_rows_mem q s j r).mpr
  cases hb : ValiantXor.rowOccupied (actualXorWord q s j) r
  · rfl
  · have hz : (xorFibre q s j false r).card+1=1 := by
      simpa [xorBoundary,hb,ValiantXor.bitNat] using hone
    omega

/-- Canonical local row order is taken from the old literal template,
while every entry is the original captured internal edge index. -/
def xorIndices (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length) :
    List XorIndex :=
  (ValiantXor.rows (actualXorWord q s j)).attach.map (xorRowIndex q s j)
def xorEdgesCapture (q : Input) (s : Selection (keyGraph q)) (j : Fin (occurrences q.val).length) :
    List ValiantXor.Edge := (xorIndices q s j).map localEdge

theorem xor_indices_nodup (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) : (xorIndices q s j).Nodup := by
  apply (ValiantXor.rows_nodup (actualXorWord q s j)).attach.map
  intro a b h
  apply Subtype.ext
  have ha := xor_row_index_row q s j a
  have hb := xor_row_index_row q s j b
  rw [h] at ha
  exact ha.symm.trans hb

theorem xor_indices_set (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    (xorIndices q s j).toFinset=xorSelected q s j := by
  ext e
  simp only [List.mem_toFinset,xorIndices,List.mem_map]
  constructor
  · rintro ⟨r,_,hr⟩
    rw [← hr]
    exact xor_row_index_mem q s j r
  · intro he
    let r := (localEdge e).1
    have hr := xor_selected_row_available q s j e he
    let r' : {r : ValiantXor.Vertex // r∈ValiantXor.rows (actualXorWord q s j)} := ⟨r,hr⟩
    refine ⟨r',by simp,?_⟩
    exact xor_row_unique q s j r hr _ e (xor_row_index_mem q s j r') he
      (xor_row_index_row q s j r') rfl

theorem xor_edges_rows (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    (xorEdgesCapture q s j).map Prod.fst=ValiantXor.rows (actualXorWord q s j) := by
  simp only [xorEdgesCapture,xorIndices,List.map_map]
  have h : (fun r : {r : ValiantXor.Vertex // r∈ValiantXor.rows (actualXorWord q s j)} =>
      (localEdge (xorRowIndex q s j r)).1)=Subtype.val := by
    funext r
    exact xor_row_index_row q s j r
  change ((ValiantXor.rows (actualXorWord q s j)).attach.map
    (fun r => (localEdge (xorRowIndex q s j r)).1))=_
  rw [h,List.attach_map_subtype_val]

private theorem count_map_card {α β : Type} [DecidableEq α] [DecidableEq β]
    (xs : List α) (hn : xs.Nodup) (f : α → β) (b : β) :
    (xs.map f).count b=(xs.toFinset.filter (fun a => f a=b)).card := by
  have hc : (xs.map f).count b=(xs.filter (fun a => decide (f a=b))).length := by
    simp [List.count,List.countP_map,List.countP_eq_length_filter,List.filter_map,Function.comp_def,Bool.beq_eq_decide_eq]
  have hs : (xs.filter (fun a => decide (f a=b))).toFinset=
      xs.toFinset.filter (fun a => f a=b) := by ext a; simp
  rw [hc,← List.toFinset_card_of_nodup (hn.filter _),hs]

theorem xor_edges_columns (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ((xorEdgesCapture q s j).map Prod.snd).Perm (ValiantXor.columns (actualXorWord q s j)) := by
  apply List.perm_iff_count.mpr
  intro r
  have hc : ((xorEdgesCapture q s j).map Prod.snd).count r=(xorFibre q s j true r).card := by
    simp only [xorEdgesCapture,List.map_map]
    rw [count_map_card _ (xor_indices_nodup q s j),xor_indices_set]
    rfl
  have hi := xor_incidence_card q s j true r
  have ho := ValiantXor.columns_exactly_once (actualXorWord q s j) r
  rw [hc]
  change (xorFibre q s j true r).card+
    ValiantXor.bitNat (ValiantXor.columnOccupied (actualXorWord q s j) r)=1 at hi
  omega

theorem xor_capture_legal (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ValiantXor.LegalMatching (actualXorWord q s j) (xorEdgesCapture q s j) :=
  ⟨xor_edges_rows q s j,xor_edges_columns q s j⟩
theorem xor_capture_active (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ∀ e∈xorEdgesCapture q s j,e∈ValiantXor.template.edges := by
  intro e he
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp he
  exact local_edge_active i

/-- The SAME captured ten-record selection is an actual local completion.
This does not identify a single matching with a cancellation support bit. -/
theorem xor_capture_complete (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ∃! cs,cs∈ValiantXor.actualCompletions (actualXorWord q s j) ∧
      ValiantXor.completionEdges (actualXorWord q s j) cs=xorEdgesCapture q s j :=
  ValiantXor.actual_matching_complete _ _ (xor_capture_legal q s j) (xor_capture_active q s j)
def xorCompletionCapture (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    {cs : List ValiantXor.Vertex // cs∈ValiantXor.actualCompletions (actualXorWord q s j)} :=
  ⟨Classical.choose (xor_capture_complete q s j),
    (Classical.choose_spec (xor_capture_complete q s j)).1.1⟩
theorem xor_completion_edges (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ValiantXor.completionEdges (actualXorWord q s j) (xorCompletionCapture q s j).val=
      xorEdgesCapture q s j :=
  (Classical.choose_spec (xor_capture_complete q s j)).1.2


theorem local_edge_injective : Function.Injective localEdge := by
  intro a b h
  have hi := (ValiantXor.template_edges_nodup).get_inj_iff.mp h
  exact Fin.ext (congrArg Fin.val hi)

theorem xor_completion_lookup (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) (e : XorIndex) :
    localEdge e∈ValiantXor.completionEdges (actualXorWord q s j) (xorCompletionCapture q s j).val ↔
      lookup q s (2,j.val,e.val,false)=true := by
  rw [xor_completion_edges]
  simp only [xorEdgesCapture,List.mem_map]
  constructor
  · rintro ⟨i,hi,hie⟩
    have hi' : i=e := local_edge_injective hie
    subst i
    have hs : e∈xorSelected q s j := by
      rw [← xor_indices_set]
      exact List.mem_toFinset.mpr hi
    simpa [xorSelected] using hs
  · intro he
    have hs : e∈xorSelected q s j := by simp [xorSelected,he]
    have hi : e∈xorIndices q s j := by
      apply List.mem_toFinset.mp
      rw [xor_indices_set]
      exact hs
    exact ⟨e,hi,rfl⟩

abbrev XorMatching (t : ValiantXor.Word) :=
  {cs : List ValiantXor.Vertex // cs∈ValiantXor.actualCompletions t}

/-- Four independent original connector vectors and the actual local
matchings. This records choices before the XOR signed sum is cancelled. -/
structure Joint (q : Input) where
  a : Source.Bits q
  b : Source.Bits q
  c : Source.Bits q
  d : Source.Bits q
  remaining : Source.RemainingMatching q a c
  clause : (i : Fin q.val.2.length) →
    Cycle.Matching (Source.boundary q i.val b) (Source.boundary q i.val d)
  xor : (j : Fin (occurrences q.val).length) → XorMatching ![c j,d j,a j,b j]

def capture (q : Input) (s : Selection (keyGraph q)) : Joint q where
  a := variableIncoming q s
  b := clauseIncoming q s
  c := variableOutgoing q s
  d := clauseOutgoing q s
  remaining := remainingCapture q s
  clause := clauseMatchingCapture q s
  xor := xorCompletionCapture q s

/-- Literal merge on the same four segment IDs. The fourth connector
component is kept; local XOR membership refers to its actual completion
edge list, including every signed alternative before cancellation. -/
def mergeWord (q : Input) (z : Joint q) (k : KeyID) : Bool :=
  match k.1 with
  | 0 => if hv : k.2.1<q.val.1 then
      if hi : k.2.2.1<slots q.val then
        if k.2.2.2 then (z.remaining.val ⟨k.2.1,hv⟩ ⟨k.2.2.1,hi⟩).2
          else (z.remaining.val ⟨k.2.1,hv⟩ ⟨k.2.2.1,hi⟩).1
      else false
    else false
  | 1 => if hc : k.2.1<q.val.2.length then
      if hi : k.2.2.1<slots q.val then
        if k.2.2.2 then ((z.clause ⟨k.2.1,hc⟩).val ⟨k.2.2.1,hi⟩).2
          else ((z.clause ⟨k.2.1,hc⟩).val ⟨k.2.2.1,hi⟩).1
      else false
    else false
  | 2 => if hj : k.2.1<(occurrences q.val).length then
      if he : k.2.2.1<xorLocal.length then
        decide (localEdge ⟨k.2.2.1,he⟩∈ValiantXor.completionEdges
          ![z.c ⟨k.2.1,hj⟩,z.d ⟨k.2.1,hj⟩,z.a ⟨k.2.1,hj⟩,z.b ⟨k.2.1,hj⟩]
          (z.xor ⟨k.2.1,hj⟩).val)
      else false
    else false
  | 3 => if hj : k.2.1<(occurrences q.val).length then
      match k.2.2.1 with
      | 0 => z.a ⟨k.2.1,hj⟩
      | 1 => z.c ⟨k.2.1,hj⟩
      | 2 => z.b ⟨k.2.1,hj⟩
      | 3 => z.d ⟨k.2.1,hj⟩
      | _ => false
    else false
  | _ => false
def mergeIDs (q : Input) (z : Joint q) : Finset KeyID :=
  (keys q).toFinset.filter (fun k => mergeWord q z k=true)

theorem merge_capture_word (q : Input) (s : Selection (keyGraph q)) (k : KeyID) (hk : k∈keys q) :
    mergeWord q (capture q s) k=lookup q s k := by
  have hks : k∈variableKeys q ∨ k∈clauseKeys q ∨ k∈xorKeys q ∨ k∈connectorKeys q := by
    simpa only [keys,List.mem_append,or_assoc] using hk
  rcases hks with hk | hk | hk | hk
  · obtain ⟨v,hv,i,hi,b,hk⟩ := variable_key_spec q k hk
    cases b <;>
      simp [mergeWord,hk,hv,hi,capture,remainingCapture,variableCapture]
  · obtain ⟨c,hc,i,hi,b,hk⟩ := clause_key_spec q k hk
    cases b <;>
      simp [mergeWord,hk,hc,hi,capture,clauseMatchingCapture,clauseCapture]
  · obtain ⟨j,hj,e,he,hk⟩ := xor_key_spec q k hk
    let j' : Fin (occurrences q.val).length := ⟨j,hj⟩
    let e' : XorIndex := ⟨e,he⟩
    have hm := xor_completion_lookup q s j' e'
    have hd : decide (localEdge e'∈ValiantXor.completionEdges (actualXorWord q s j')
        (xorCompletionCapture q s j').val)=lookup q s (2,j,e,false) := by
      cases hb : lookup q s (2,j,e,false)
      · have hn : localEdge e'∉ValiantXor.completionEdges (actualXorWord q s j')
            (xorCompletionCapture q s j').val := by simpa [e',j',hb] using hm
        simp [hn]
      · have hp := hm.mpr (by simpa [e',j'] using hb)
        simp [hp]
    subst k
    simpa [mergeWord,hj,he,capture,actualXorWord,j',e'] using hd
  · obtain ⟨j,hj,e,he,hk⟩ := connector_key_spec q k hk
    interval_cases e <;>
      simp [mergeWord,hk,hj,capture,variableIncoming,variableOutgoing,clauseIncoming,clauseOutgoing]

/-- First inverse: capture and literal merge recover every original
occurrence ID, with no post-cancellation matching identification. -/
theorem merge_capture (q : Input) (s : Selection (keyGraph q)) :
    mergeIDs q (capture q s)=selectedIDs q s := by
  ext k
  simp only [mergeIDs,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨hk,hs⟩
    rw [merge_capture_word q s k hk] at hs
    simpa [lookup] using hs
  · intro hs
    have hk := selectedIDs_mem_keys q s k hs
    exact ⟨hk,by rw [merge_capture_word q s k hk]; simp [lookup,hs]⟩

theorem selectedIDs_membership (q : Input) (s : Selection (keyGraph q)) (k : Keys q) :
    k.val∈selectedIDs q s ↔ k∈s.val := by
  constructor
  · intro h
    obtain ⟨e,he,hk⟩ := Finset.mem_image.mp h
    have hek : e=k := Subtype.ext hk
    simpa [hek] using he
  · intro h
    exact Finset.mem_image.mpr ⟨k,h,rfl⟩
theorem capture_injective (q : Input) : Function.Injective (capture q) := by
  intro s t h
  have hm := congrArg (mergeIDs q) h
  rw [merge_capture,merge_capture] at hm
  apply Subtype.ext
  ext k
  rw [← selectedIDs_membership q s k,← selectedIDs_membership q t k,hm]

def mergeWeight (q : Input) (z : Joint q) : ℤ :=
  ∏ k∈mergeIDs q z,if (record q k).2 then -1 else 1

/-- Signed product transport for the first inverse, still BEFORE local
sums. No negative local completion or repeated ambient occurrence is lost. -/
theorem merge_capture_weight (q : Input) (s : Selection (keyGraph q)) :
    mergeWeight q (capture q s)=selectionWeight (keyGraph q) s := by
  rw [mergeWeight,merge_capture]
  unfold selectedIDs selectionWeight
  rw [Finset.prod_image]
  · rfl
  · intro a _ b _ h
    exact Subtype.ext h


def xorSelectedWeight (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) : ℤ :=
  ∏ e∈xorSelected q s j,ValiantXor.matrix (localEdge e).1 (localEdge e).2

/-- The signed weight of the actual captured local completion is exactly
the product of its original selected internal records, including -1 edges. -/
theorem xor_completion_weight (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ValiantXor.completionWeight (actualXorWord q s j) (xorCompletionCapture q s j).val=
      xorSelectedWeight q s j := by
  unfold ValiantXor.completionWeight
  rw [xor_completion_edges]
  simp only [xorEdgesCapture,List.map_map]
  change ((xorIndices q s j).map (fun e => ValiantXor.matrix (localEdge e).1 (localEdge e).2)).prod=_
  rw [← List.prod_toFinset _ (xor_indices_nodup q s j),xor_indices_set]
  rfl

theorem xor_completion_raw_weight (q : Input) (s : Selection (keyGraph q))
    (j : Fin (occurrences q.val).length) :
    ValiantXor.completionWeight (actualXorWord q s j) (xorCompletionCapture q s j).val=
      ∏ e∈xorSelected q s j,if (record q (2,j.val,e.val,false)).2 then (-1 : ℤ) else 1 := by
  rw [xor_completion_weight]
  apply Finset.prod_congr rfl
  intro e _
  exact (local_record_weight q j e).symm

def clauseSelectedWeight (q : Input) (s : Selection (keyGraph q))
    (c : Fin q.val.2.length) : ℤ :=
  ∏ i : Fin (slots q.val),
    if lookup q s (1,c.val,i.val,true) && decide (i.val=(occurrences q.val).length) then -1 else 1

theorem clause_capture_weight (q : Input) (s : Selection (keyGraph q))
    (c : Fin q.val.2.length) :
    clauseSelectedWeight q s c=Cycle.closingWeight (clauseCapture q s c) := by
  unfold clauseSelectedWeight
  have hp : (∏ i : Fin (slots q.val),
      if lookup q s (1,c.val,i.val,true) && decide (i.val=(occurrences q.val).length) then (-1 : ℤ) else 1)=
      (if lookup q s (1,c.val,(occurrences q.val).length,true) then (-1 : ℤ) else 1) := by
    calc
      _ = (if lookup q s (1,c.val,(Fin.last (occurrences q.val).length).val,true) &&
          decide ((Fin.last (occurrences q.val).length).val=(occurrences q.val).length) then (-1 : ℤ) else 1) := by
        apply Finset.prod_eq_single (Fin.last (occurrences q.val).length)
        · intro i _ hi
          have hn : i.val≠(occurrences q.val).length := by
            intro he
            exact hi (Fin.ext he)
          simp [hn]
        · simp
      _ = _ := by simp
  simpa [Cycle.closingWeight,clauseCapture] using hp


/-- Actual typed original occurrence selection assembled by the literal
four-segment merge. Its global Selected law is still a separate obligation. -/
def typedMerge (q : Input) (z : Joint q) : Finset (Keys q) :=
  Finset.univ.filter (fun k => mergeWord q z k.val=true)
theorem typed_merge_image (q : Input) (z : Joint q) :
    (typedMerge q z).image Subtype.val=mergeIDs q z := by
  ext k
  simp only [Finset.mem_image,typedMerge,Finset.mem_filter,Finset.mem_univ,true_and,
    mergeIDs,List.mem_toFinset]
  constructor
  · rintro ⟨e,he,hk⟩
    exact ⟨by simpa only [hk] using List.mem_toFinset.mp e.property,by simpa only [hk] using he⟩
  · rintro ⟨hk,he⟩
    exact ⟨⟨k,List.mem_toFinset.mpr hk⟩,he,rfl⟩
theorem typed_merge_capture (q : Input) (s : Selection (keyGraph q)) :
    typedMerge q (capture q s)=s.val := by
  ext k
  simp only [typedMerge,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [merge_capture_word q s k.val (List.mem_toFinset.mp k.property)]
  simpa [lookup] using selectedIDs_membership q s k

/-- The internally saved erasure law really forbids each removed cycle
occurrence. This is also needed in the reverse direction: filtering by the
physical key list cannot silently discard a selected local edge. -/
theorem remaining_deleted_zero (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) (b : Bool) (hm : isMarked q.val v.val i.val b=true) :
    (if b then (z.remaining.val v i).2 else (z.remaining.val v i).1)=false := by
  have hi : i.val<(occurrences q.val).length := by
    by_contra hi
    simp [isMarked,hi] at hm
  have hv : (occurrence q.val i.val).2.1=v.val := by
    by_contra hv
    simp [isMarked,hv] at hm
  have he := congrArg (fun f : Source.FamilyChoice q => f v i) z.remaining.property.1
  cases b <;> cases hp : (occurrence q.val i.val).2.2
  · simp [isMarked,hi,hv,hp] at hm
  · have hd := congrArg Prod.fst he
    simpa [Source.erase,hi,hv,hp] using hd.symm
  · have hs := congrArg Prod.snd he
    simpa [Source.erase,hi,hv,hp] using hs.symm
  · simp [isMarked,hi,hv,hp] at hm

theorem merge_variable_support (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) (b : Bool) :
    (0,v.val,i.val,b)∈mergeIDs q z ↔
      (if b then (z.remaining.val v i).2 else (z.remaining.val v i).1)=true := by
  have hw : mergeWord q z (0,v.val,i.val,b)=
      (if b then (z.remaining.val v i).2 else (z.remaining.val v i).1) := by
    cases b <;> simp [mergeWord,v.isLt,i.isLt]
  constructor
  · intro h
    have he := (Finset.mem_filter.mp h).2
    rwa [hw] at he
  · intro h
    have hn : isMarked q.val v.val i.val b=false := by
      cases hb : isMarked q.val v.val i.val b
      · rfl
      · have hz := remaining_deleted_zero q z v i b hb
        rw [hz] at h
        contradiction
    have hk := (variable_key_member q v.val i.val b).mpr ⟨v.isLt,i.isLt,hn⟩
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hk,hw.trans h⟩


theorem mergeIDs_mem_keys (q : Input) (z : Joint q) (k : KeyID) (hk : k∈mergeIDs q z) :
    k∈keys q := List.mem_toFinset.mp (Finset.mem_filter.mp hk).1

theorem connector_key_member (q : Input) (j : Fin (occurrences q.val).length) (e : Fin 4) :
    (3,j.val,e.val,false)∈keys q := by
  have hk : (3,j.val,e.val,false)∈connectorKeys q :=
    List.mem_flatMap.mpr ⟨j.val,List.mem_range.mpr j.isLt,
      List.mem_map.mpr ⟨e.val,List.mem_range.mpr e.isLt,rfl⟩⟩
  simp [keys,hk]
theorem merge_connector_support (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (e : Fin 4) :
    (3,j.val,e.val,false)∈mergeIDs q z ↔ ![z.a j,z.c j,z.b j,z.d j] e=true := by
  have hk := connector_key_member q j e
  simp only [mergeIDs,Finset.mem_filter,List.mem_toFinset,hk,true_and]
  fin_cases e <;> simp [mergeWord,j.isLt]

theorem typed_merge_filter (q : Input) (z : Joint q) (side : Bool) (r : Fin (vertexCount q.val)) :
    ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=r)).image
      Subtype.val=(mergeIDs q z).filter (fun k => coordinate q side k=r.val) := by
  ext k
  simp only [Finset.mem_image,Finset.mem_filter]
  constructor
  · rintro ⟨e,⟨he,hcoord⟩,hk⟩
    have hm : k∈mergeIDs q z := by
      rw [← typed_merge_image]
      exact Finset.mem_image.mpr ⟨e,he,hk⟩
    refine ⟨hm,?_⟩
    have hv := congrArg Fin.val hcoord
    cases side
    · simpa [key_left_coordinate,hk] using hv
    · simpa [key_right_coordinate,hk] using hv
  · rintro ⟨hm,hcoord⟩
    have hi : k∈(typedMerge q z).image Subtype.val := by rwa [typed_merge_image]
    obtain ⟨e,he,hk⟩ := Finset.mem_image.mp hi
    refine ⟨e,⟨he,?_⟩,hk⟩
    apply Fin.ext
    cases side
    · simpa [key_left_coordinate,hk] using hcoord
    · simpa [key_right_coordinate,hk] using hcoord

theorem merge_variable_row_filter (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    (mergeIDs q z).filter (fun k => coordinate q false k=variableVertex q.val v.val i.val)=
      mergeIDs q z∩variableRowCandidates q v i := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈mergeIDs q z
  · simp only [hs,true_and]
    rw [variable_row_key q v i k (mergeIDs_mem_keys q z k hs)]
    by_cases hc : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val <;>
      simp [variableRowCandidates,hc,← and_assoc]
  · simp [hs]

private theorem intersection_card_sum {A : Type} [DecidableEq A] (s t : Finset A) :
    (s∩t).card=∑k∈t,if k∈s then (1 : ℕ) else 0 := by
  have he : s∩t=t.filter (fun k=>k∈s) := by ext k; simp [and_comm]
  rw [he,Finset.card_eq_sum_ones,Finset.sum_filter]

theorem merge_variable_row_bits (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    (mergeIDs q z∩variableRowCandidates q v i).card=
      Cycle.bit ((z.remaining.val v i).1)+Cycle.bit ((z.remaining.val v i).2)+
        (if h : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
          then Cycle.bit (z.a ⟨i.val,h.1⟩) else 0) := by
  have hd := merge_variable_support q z v i false
  have hs := merge_variable_support q z v i true
  change (0,v.val,i.val,false)∈mergeIDs q z ↔ (z.remaining.val v i).1=true at hd
  change (0,v.val,i.val,true)∈mergeIDs q z ↔ (z.remaining.val v i).2=true at hs
  rw [intersection_card_sum]
  by_cases h : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
  · have ha := merge_connector_support q z ⟨i.val,h.1⟩ 0
    change (3,i.val,0,false)∈mergeIDs q z ↔ z.a ⟨i.val,h.1⟩=true at ha
    simp [-Finset.sum_boole,-Finset.sum_ite_mem,variableRowCandidates,h,hd,hs,ha,Cycle.bit,Nat.add_assoc]
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,variableRowCandidates,h,hd,hs,Cycle.bit]

/-- First reverse validity body: assembling the independent local
choices gives exact-one at every original VARIABLE row. In particular the
physical list's deleted edge is never a silently lost local choice. -/
theorem merge_variable_rows (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    ((typedMerge q z).filter (fun k => (keyGraph q).left k=
      ⟨variableVertex q.val v.val i.val,variableVertex_lt q.val v.val i.val v.isLt i.isLt⟩)).card=1 := by
  let r : Fin (vertexCount q.val) := ⟨variableVertex q.val v.val i.val,
    variableVertex_lt q.val v.val i.val v.isLt i.isLt⟩
  have hm := congrArg Finset.card (typed_merge_filter q z false r)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hm
  change ((typedMerge q z).filter (fun k => (keyGraph q).left k=r)).card=
    ((mergeIDs q z).filter (fun k => coordinate q false k=variableVertex q.val v.val i.val)).card at hm
  rw [merge_variable_row_filter,merge_variable_row_bits] at hm
  have hr := z.remaining.property.2.1 v i
  have hone : Cycle.bit ((z.remaining.val v i).1)+Cycle.bit ((z.remaining.val v i).2)+
      (if h : i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val
        then Cycle.bit (z.a ⟨i.val,h.1⟩) else 0)=1 := by
    by_cases hi : i.val<(occurrences q.val).length
    · by_cases hv : (occurrence q.val i.val).2.1=v.val
      · cases hp : (occurrence q.val i.val).2.2
        · have hz := remaining_deleted_zero q z v i true (by simp [isMarked,hi,hv,hp])
          change (z.remaining.val v i).2=false at hz
          simpa [Source.restore,hi,hv,hp,hz,Cycle.bit] using hr
        · have hz := remaining_deleted_zero q z v i false (by simp [isMarked,hi,hv,hp])
          change (z.remaining.val v i).1=false at hz
          have he : Cycle.bit (z.a ⟨i.val,hi⟩)+Cycle.bit ((z.remaining.val v i).2)=1 := by
            simpa [Source.restore,hi,hv,hp,Cycle.bit] using hr
          simp only [hz,Cycle.bit,Bool.false_eq_true,ite_false,Nat.zero_add]
          simpa only [dif_pos (show i.val<(occurrences q.val).length ∧ (occurrence q.val i.val).2.1=v.val from ⟨hi,hv⟩),Cycle.bit] using
            (Nat.add_comm (Cycle.bit ((z.remaining.val v i).2)) (Cycle.bit (z.a ⟨i.val,hi⟩))).trans he
      · simpa [Source.restore,hi,hv] using hr
    · simpa [Source.restore,hi] using hr
  exact hm.trans hone


theorem merge_variable_column_filter (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    (mergeIDs q z).filter (fun k => coordinate q true k=
        variableVertex q.val v.val (Cycle.next (occurrences q.val).length i).val)=
      mergeIDs q z∩variableColumnCandidates q v i := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈mergeIDs q z
  · simp only [hs,true_and]
    rw [variable_column_key q v i k (mergeIDs_mem_keys q z k hs)]
    simp only [variableColumnCandidates,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    split_ifs <;> simp_all only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,false_or,true_and,and_true] <;> tauto
  · simp [hs]

theorem merge_variable_column_bits (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    let t := Cycle.next (occurrences q.val).length i
    (mergeIDs q z∩variableColumnCandidates q v i).card=
      Cycle.bit ((z.remaining.val v t).1)+Cycle.bit ((z.remaining.val v i).2)+
        (if h : positiveColumn q v t then Cycle.bit (z.c ⟨t.val,h.1⟩) else 0)+
        (if h : negativeColumn q v i then Cycle.bit (z.c ⟨i.val,h.1⟩) else 0) := by
  dsimp only
  let t := Cycle.next (occurrences q.val).length i
  have hd := merge_variable_support q z v t false
  have hs := merge_variable_support q z v i true
  change (0,v.val,t.val,false)∈mergeIDs q z ↔ (z.remaining.val v t).1=true at hd
  change (0,v.val,i.val,true)∈mergeIDs q z ↔ (z.remaining.val v i).2=true at hs
  have ha (h : positiveColumn q v t) :
      (3,t.val,1,false)∈mergeIDs q z ↔ z.c ⟨t.val,h.1⟩=true := by
    simpa using merge_connector_support q z ⟨t.val,h.1⟩ 1
  have hb (h : negativeColumn q v i) :
      (3,i.val,1,false)∈mergeIDs q z ↔ z.c ⟨i.val,h.1⟩=true := by
    simpa using merge_connector_support q z ⟨i.val,h.1⟩ 1
  have hne (hn : negativeColumn q v i) : t.val≠i.val := by
    rw [← nextSlot_rotate q.val i]
    exact nextSlot_ne_of_nonempty q i (by unfold negativeColumn at hn; omega)
  rw [intersection_card_sum]
  change (∑k∈({(0,v.val,t.val,false),(0,v.val,i.val,true)} ∪
    (if positiveColumn q v t then {(3,t.val,1,false)} else ∅) ∪
    (if negativeColumn q v i then {(3,i.val,1,false)} else ∅)),
      if k∈mergeIDs q z then (1 : ℕ) else 0)=
        Cycle.bit ((z.remaining.val v t).1)+Cycle.bit ((z.remaining.val v i).2)+
          (if h : positiveColumn q v t then Cycle.bit (z.c ⟨t.val,h.1⟩) else 0)+
          (if h : negativeColumn q v i then Cycle.bit (z.c ⟨i.val,h.1⟩) else 0)
  by_cases hp : positiveColumn q v t <;> by_cases hn : negativeColumn q v i
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,hd,hs,ha hp,hb hn,hne hn,Ne.symm (hne hn),Cycle.bit,Nat.add_assoc]
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,hd,hs,ha hp,Cycle.bit,Nat.add_assoc]
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,hd,hs,hb hn,Cycle.bit,Nat.add_assoc]
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hp,hn,Finset.insert_union,hd,hs,Cycle.bit,Nat.add_assoc]

/-- Reverse exact-one at the column next i. The two possible connector1
records are independent positive/negative occurrences and are never merged. -/
theorem merge_variable_columns (q : Input) (z : Joint q) (v : Fin q.val.1)
    (i : Fin (slots q.val)) :
    ((typedMerge q z).filter (fun k => (keyGraph q).right k=
      ⟨variableVertex q.val v.val (Cycle.next (occurrences q.val).length i).val,
        variableVertex_lt q.val v.val _ v.isLt (Cycle.next _ i).isLt⟩)).card=1 := by
  let t := Cycle.next (occurrences q.val).length i
  let r : Fin (vertexCount q.val) := ⟨variableVertex q.val v.val t.val,
    variableVertex_lt q.val v.val t.val v.isLt t.isLt⟩
  have hm := congrArg Finset.card (typed_merge_filter q z true r)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hm
  change ((typedMerge q z).filter (fun k => (keyGraph q).right k=r)).card=
    ((mergeIDs q z).filter (fun k => coordinate q true k=variableVertex q.val v.val t.val)).card at hm
  rw [merge_variable_column_filter,merge_variable_column_bits] at hm
  have hd : Cycle.bit ((Source.restore q z.c z.remaining.val v t).1)=
      Cycle.bit ((z.remaining.val v t).1)+
        (if h : positiveColumn q v t then Cycle.bit (z.c ⟨t.val,h.1⟩) else 0) := by
    by_cases hp : positiveColumn q v t
    · have hz := remaining_deleted_zero q z v t false (by simp [isMarked,hp.1,hp.2.1,hp.2.2])
      change (z.remaining.val v t).1=false at hz
      simp [Source.restore,hp.1,hp.2.1,hp.2.2,hp,hz,Cycle.bit]
    · have he : (Source.restore q z.c z.remaining.val v t).1=(z.remaining.val v t).1 := by
        unfold Source.restore
        split_ifs with hi hv hb
        · exact False.elim (hp ⟨hi,hv,hb⟩)
        all_goals rfl
      rw [he]
      simp [hp]
  have hs : Cycle.bit ((Source.restore q z.c z.remaining.val v i).2)=
      Cycle.bit ((z.remaining.val v i).2)+
        (if h : negativeColumn q v i then Cycle.bit (z.c ⟨i.val,h.1⟩) else 0) := by
    by_cases hp : negativeColumn q v i
    · have hz := remaining_deleted_zero q z v i true (by simp [isMarked,hp.1,hp.2.1,hp.2.2])
      change (z.remaining.val v i).2=false at hz
      simp [Source.restore,hp.1,hp.2.1,hp.2.2,hp,hz,Cycle.bit]
    · have he : (Source.restore q z.c z.remaining.val v i).2=(z.remaining.val v i).2 := by
        unfold Source.restore
        split_ifs with hi hv hb
        · rfl
        · exact False.elim (hp ⟨hi,hv,by simpa using hb⟩)
        all_goals rfl
      rw [he]
      simp [hp]
  have hc := z.remaining.property.2.2 v i
  rw [hd,hs] at hc
  have hone : Cycle.bit ((z.remaining.val v t).1)+Cycle.bit ((z.remaining.val v i).2)+
      (if h : positiveColumn q v t then Cycle.bit (z.c ⟨t.val,h.1⟩) else 0)+
      (if h : negativeColumn q v i then Cycle.bit (z.c ⟨i.val,h.1⟩) else 0)=1 := by omega
  exact hm.trans hone


theorem clause_key_member (q : Input) (c : Fin q.val.2.length) (i : Fin (slots q.val)) (b : Bool) :
    (1,c.val,i.val,b)∈keys q := by
  have hk : (1,c.val,i.val,b)∈clauseKeys q := by
    apply List.mem_flatMap.mpr
    refine ⟨c.val,List.mem_range.mpr c.isLt,?_⟩
    apply List.mem_flatMap.mpr
    refine ⟨i.val,List.mem_range.mpr i.isLt,?_⟩
    cases b <;> simp
  simp [keys,hk]

theorem merge_clause_support (q : Input) (z : Joint q) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (b : Bool) :
    (1,c.val,i.val,b)∈mergeIDs q z ↔
      (if b then ((z.clause c).val i).2 else ((z.clause c).val i).1)=true := by
  have hk := clause_key_member q c i b
  simp only [mergeIDs,Finset.mem_filter,List.mem_toFinset,hk,true_and]
  cases b <;> simp [mergeWord,c.isLt,i.isLt]

theorem merge_clause_filter (q : Input) (z : Joint q) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    (mergeIDs q z).filter (fun k => coordinate q side k=clauseVertex q.val c.val t.val)=
      mergeIDs q z∩clauseCandidates q c i side := by
  let t := if side then Cycle.next (occurrences q.val).length i else i
  ext k
  simp only [Finset.mem_filter,Finset.mem_inter]
  by_cases hs : k∈mergeIDs q z
  · simp only [hs,true_and]
    have hf := clause_key_fibre q c i side k (mergeIDs_mem_keys q z k hs)
    dsimp only at hf
    rw [hf]
    simp only [clauseCandidates,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton]
    split_ifs <;> simp_all only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton,Finset.notMem_empty,or_false,false_or,true_and,and_true] <;> tauto
  · simp [hs]

theorem merge_clause_bits (q : Input) (z : Joint q) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    (mergeIDs q z∩clauseCandidates q c i side).card=
      Cycle.bit (((z.clause c).val t).1)+Cycle.bit (((z.clause c).val i).2)+
        Cycle.bit (Source.boundary q c.val (if side then z.d else z.b) t) := by
  dsimp only
  let t := if side then Cycle.next (occurrences q.val).length i else i
  have hd := merge_clause_support q z c t false
  have hs := merge_clause_support q z c i true
  change (1,c.val,t.val,false)∈mergeIDs q z ↔ ((z.clause c).val t).1=true at hd
  change (1,c.val,i.val,true)∈mergeIDs q z ↔ ((z.clause c).val i).2=true at hs
  have ha (h : t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val) :
      (3,t.val,(if side then 3 else 2),false)∈mergeIDs q z ↔
        (if side then z.d else z.b) ⟨t.val,h.1⟩=true := by
    cases side
    · simpa using merge_connector_support q z ⟨t.val,h.1⟩ 2
    · simpa using merge_connector_support q z ⟨t.val,h.1⟩ 3
  rw [intersection_card_sum]
  change (∑k∈({(1,c.val,t.val,false),(1,c.val,i.val,true)} ∪
    (if t.val<(occurrences q.val).length ∧ (occurrence q.val t.val).1=c.val
      then {(3,t.val,(if side then 3 else 2),false)} else ∅)),
        if k∈mergeIDs q z then (1 : ℕ) else 0)=
          Cycle.bit (((z.clause c).val t).1)+Cycle.bit (((z.clause c).val i).2)+
            Cycle.bit (Source.boundary q c.val (if side then z.d else z.b) t)
  by_cases hi : t.val<(occurrences q.val).length
  · by_cases he : (occurrence q.val t.val).1=c.val
    · have hb := ha ⟨hi,he⟩
      simp [-Finset.sum_boole,-Finset.sum_ite_mem,hi,he,hd,hs,hb,Source.boundary,Cycle.bit,Nat.add_assoc]
    · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hi,he,hd,hs,Source.boundary,Cycle.bit]
  · simp [-Finset.sum_boole,-Finset.sum_ite_mem,hi,hd,hs,Source.boundary,Cycle.bit]

/-- Reverse exact-one at BOTH original sides of a clause cycle. Its
dummy slot, closing sign and two distinct external connectors are kept. -/
theorem merge_clause_nodes (q : Input) (z : Joint q) (c : Fin q.val.2.length)
    (i : Fin (slots q.val)) (side : Bool) :
    let t := if side then Cycle.next (occurrences q.val).length i else i
    ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=
      ⟨clauseVertex q.val c.val t.val,clauseVertex_lt q.val c.val t.val c.isLt t.isLt⟩)).card=1 := by
  let t := if side then Cycle.next (occurrences q.val).length i else i
  let r : Fin (vertexCount q.val) := ⟨clauseVertex q.val c.val t.val,
    clauseVertex_lt q.val c.val t.val c.isLt t.isLt⟩
  have hm := congrArg Finset.card (typed_merge_filter q z side r)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hm
  change ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=r)).card=
    ((mergeIDs q z).filter (fun k => coordinate q side k=clauseVertex q.val c.val t.val)).card at hm
  rw [merge_clause_filter,merge_clause_bits] at hm
  have hone : Cycle.bit (((z.clause c).val t).1)+Cycle.bit (((z.clause c).val i).2)+
      Cycle.bit (Source.boundary q c.val (if side then z.d else z.b) t)=1 := by
    cases side
    · exact (z.clause c).property.1 i
    · exact (z.clause c).property.2 i
  exact hm.trans hone


def jointXorWord (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) : ValiantXor.Word :=
  ![z.c j,z.d j,z.a j,z.b j]
def jointXorEdges (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    List ValiantXor.Edge := ValiantXor.completionEdges (jointXorWord q z j) (z.xor j).val
def jointXorIndices (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) : Finset XorIndex :=
  Finset.univ.filter (fun e => localEdge e∈jointXorEdges q z j)
def jointXorFibre (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) : Finset XorIndex :=
  (jointXorIndices q z j).filter (fun e => localCoordinate side e=r)
def jointXorBoundary (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) : Bool :=
  if side then ValiantXor.columnOccupied (jointXorWord q z j) r
    else ValiantXor.rowOccupied (jointXorWord q z j) r

theorem merge_xor_support (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) (e : XorIndex) :
    (2,j.val,e.val,false)∈mergeIDs q z ↔ localEdge e∈jointXorEdges q z j := by
  have hk := xor_key_member q j e
  simp [mergeIDs,mergeWord,j.isLt,e.isLt,hk,jointXorEdges,jointXorWord]

theorem local_edge_surjective (e : ValiantXor.Edge) (he : e∈ValiantXor.template.edges) :
    ∃ i : XorIndex,localEdge i=e := by
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp he
  let i' : XorIndex := ⟨i.val,by simpa [xorLocal,ValiantXor.template] using i.isLt⟩
  exact ⟨i',by simpa [localEdge,i',ValiantXor.template] using hi⟩

theorem joint_xor_edges_active (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (e : ValiantXor.Edge) (he : e∈jointXorEdges q z j) : e∈ValiantXor.template.edges :=
  ValiantXor.actual_matching_edges _ _ (z.xor j).property e he
theorem joint_xor_edges_nodup (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    (jointXorEdges q z j).Nodup := by
  apply List.Nodup.of_map Prod.fst
  rw [jointXorEdges,jointXorWord,(ValiantXor.completion_maps _ _ (List.mem_filter.mp (z.xor j).property).1).1]
  exact ValiantXor.rows_nodup _

theorem joint_xor_fibre_image (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (jointXorFibre q z j side r).image localEdge=
      (jointXorEdges q z j).toFinset.filter (fun e => (if side then e.2 else e.1)=r) := by
  ext e
  simp only [Finset.mem_image,Finset.mem_filter,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,rfl⟩
    obtain ⟨hs,hc⟩ := Finset.mem_filter.mp hi
    have hm := (Finset.mem_filter.mp hs).2
    exact ⟨hm,hc⟩
  · rintro ⟨he,hc⟩
    obtain ⟨i,hi⟩ := local_edge_surjective e (joint_xor_edges_active q z j e he)
    refine ⟨i,?_,hi⟩
    apply Finset.mem_filter.mpr
    constructor
    · simp [jointXorIndices,hi,he]
    · simpa [localCoordinate,hi] using hc

theorem joint_xor_fibre_card (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (jointXorFibre q z j side r).card=
      ((jointXorEdges q z j).map (fun e => if side then e.2 else e.1)).count r := by
  have h := congrArg Finset.card (joint_xor_fibre_image q z j side r)
  rw [Finset.card_image_of_injective _ local_edge_injective] at h
  rw [count_map_card _ (joint_xor_edges_nodup q z j)]
  exact h

theorem joint_xor_boundary_word (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) (hr : r.val<2) :
    xorConnectorID j side r∈mergeIDs q z ↔ jointXorBoundary q z j side r=true := by
  fin_cases r <;> cases side <;> simp only [Fin.reduceFinMk] at hr
  all_goals first
    | omega
    | simpa [xorConnectorID,jointXorBoundary,jointXorWord,
        ValiantXor.rowOccupied,ValiantXor.columnOccupied] using merge_connector_support q z j 0
    | simpa [xorConnectorID,jointXorBoundary,jointXorWord,
        ValiantXor.rowOccupied,ValiantXor.columnOccupied] using merge_connector_support q z j 1
    | simpa [xorConnectorID,jointXorBoundary,jointXorWord,
        ValiantXor.rowOccupied,ValiantXor.columnOccupied] using merge_connector_support q z j 2
    | simpa [xorConnectorID,jointXorBoundary,jointXorWord,
        ValiantXor.rowOccupied,ValiantXor.columnOccupied] using merge_connector_support q z j 3

theorem merge_xor_filter (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (mergeIDs q z).filter (fun k => coordinate q side k=xorVertex q.val j.val r.val)=
      ((jointXorFibre q z j side r).image (fun e => (2,j.val,e.val,false))) ∪
        (if r.val<2 ∧ jointXorBoundary q z j side r=true then {xorConnectorID j side r} else ∅) := by
  ext k
  simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_image]
  constructor
  · rintro ⟨hm,hcoord⟩
    rcases (xor_key_fibre q j side r k (mergeIDs_mem_keys q z k hm)).mp hcoord with h | h
    · obtain ⟨e,hk,he⟩ := h
      left
      refine ⟨e,?_,hk.symm⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_,he⟩
      have hp := (merge_xor_support q z j e).mp (by simpa [hk] using hm)
      simp [jointXorIndices,hp]
    · obtain ⟨hr,hk⟩ := h
      have hb := (joint_xor_boundary_word q z j side r hr).mp (by simpa [hk] using hm)
      right
      simp [hr,hb,hk]
  · rintro (⟨e,he,hk⟩ | hc)
    · obtain ⟨hm,hr⟩ := Finset.mem_filter.mp he
      have hp := (Finset.mem_filter.mp hm).2
      have hs := (merge_xor_support q z j e).mpr hp
      have hs' : k∈mergeIDs q z := by simpa [hk] using hs
      exact ⟨hs',(xor_key_fibre q j side r k (mergeIDs_mem_keys q z k hs')).mpr
        (Or.inl ⟨e,hk.symm,hr⟩)⟩
    · split_ifs at hc with h
      · obtain ⟨hr,hb⟩ := h
        have hk : k=xorConnectorID j side r := by simpa using hc
        have hs : k∈mergeIDs q z := by
          simpa [hk] using (joint_xor_boundary_word q z j side r hr).mpr hb
        exact ⟨hs,(xor_key_fibre q j side r k (mergeIDs_mem_keys q z k hs)).mpr (Or.inr ⟨hr,hk⟩)⟩
      · simp at hc

theorem joint_xor_incidence (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    (jointXorFibre q z j side r).card+ValiantXor.bitNat (jointXorBoundary q z j side r)=1 := by
  rw [joint_xor_fibre_card]
  have h := ValiantXor.actual_matching_exact_one (jointXorWord q z j) (z.xor j).val (z.xor j).property
  cases side
  · exact h.1 r
  · exact h.2 r

/-- Reverse exact-one at EVERY original XOR row and column, before
signed local cancellations and with all actual external occupations. -/
theorem merge_xor_nodes (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length)
    (side : Bool) (r : ValiantXor.Vertex) :
    ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=
      ⟨xorVertex q.val j.val r.val,xorVertex_lt q.val j.val r.val j.isLt r.isLt⟩)).card=1 := by
  let v : Fin (vertexCount q.val) := ⟨xorVertex q.val j.val r.val,
    xorVertex_lt q.val j.val r.val j.isLt r.isLt⟩
  have hm := congrArg Finset.card (typed_merge_filter q z side v)
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hm
  change ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=v)).card=
    ((mergeIDs q z).filter (fun k => coordinate q side k=xorVertex q.val j.val r.val)).card at hm
  rw [merge_xor_filter] at hm
  have hd : Disjoint ((jointXorFibre q z j side r).image (fun e => (2,j.val,e.val,false)))
      (if r.val<2 ∧ jointXorBoundary q z j side r=true then {xorConnectorID j side r} else ∅) := by
    apply Finset.disjoint_left.mpr
    intro k hk hc
    obtain ⟨e,_,rfl⟩ := Finset.mem_image.mp hk
    split_ifs at hc <;> simp [xorConnectorID] at hc
  have hinj : Function.Injective (fun e : XorIndex => (2,j.val,e.val,false)) := by
    intro a b h
    exact Fin.ext (congrArg (fun k : KeyID => k.2.2.1) h)
  rw [Finset.card_union_of_disjoint hd,Finset.card_image_of_injective _ hinj] at hm
  have hb : ¬ r.val<2 → jointXorBoundary q z j side r=false := by
    intro hr
    fin_cases r <;> cases side <;>
      simp [jointXorBoundary,jointXorWord,ValiantXor.rowOccupied,ValiantXor.columnOccupied] at *
  have hone := joint_xor_incidence q z j side r
  by_cases hr : r.val<2 <;> cases hbit : jointXorBoundary q z j side r
  all_goals simp_all [ValiantXor.bitNat,v]


private theorem block_coordinates (L N r : ℕ) (hL : 0<L) (hr : r<N*L) :
    ∃ a : Fin N,∃ i : Fin L,r=a.val*L+i.val := by
  let a : Fin N := ⟨r/L,(Nat.div_lt_iff_lt_mul hL).mpr hr⟩
  let i : Fin L := ⟨r%L,Nat.mod_lt r hL⟩
  exact ⟨a,i,by simpa [a,i,Nat.mul_comm] using (Nat.div_add_mod r L).symm⟩

/-- Complete partition of the original raw vertex addresses. No empty
block is silently removed: when the graph is empty there is no such r. -/
theorem vertex_partition (q : Input) (r : Fin (vertexCount q.val)) :
    (∃ v : Fin q.val.1,∃ i : Fin (slots q.val),r.val=variableVertex q.val v.val i.val) ∨
    (∃ c : Fin q.val.2.length,∃ i : Fin (slots q.val),r.val=clauseVertex q.val c.val i.val) ∨
    (∃ j : Fin (occurrences q.val).length,∃ a : ValiantXor.Vertex,r.val=xorVertex q.val j.val a.val) := by
  have hL : 0<slots q.val := by simp [slots]
  have hb : base q.val=q.val.1*slots q.val+q.val.2.length*slots q.val := by simp [base,Nat.add_mul]
  by_cases hv : r.val<q.val.1*slots q.val
  · obtain ⟨v,i,hi⟩ := block_coordinates (slots q.val) q.val.1 r.val hL hv
    exact Or.inl ⟨v,i,hi⟩
  · by_cases hc : r.val<base q.val
    · have htail : r.val-q.val.1*slots q.val<q.val.2.length*slots q.val := by omega
      obtain ⟨c,i,hi⟩ := block_coordinates (slots q.val) q.val.2.length
        (r.val-q.val.1*slots q.val) hL htail
      right; left
      refine ⟨c,i,?_⟩
      dsimp [clauseVertex]
      omega
    · have hr := r.isLt
      change r.val<base q.val+4*(occurrences q.val).length at hr
      have htail : r.val-base q.val<(occurrences q.val).length*4 := by omega
      obtain ⟨j,a,hi⟩ := block_coordinates 4 (occurrences q.val).length
        (r.val-base q.val) (by omega) htail
      right; right
      refine ⟨j,a,?_⟩
      dsimp [xorVertex]
      omega

theorem merge_node_card (q : Input) (z : Joint q) (side : Bool) (r : Fin (vertexCount q.val)) :
    ((typedMerge q z).filter (fun k => (if side then (keyGraph q).right k else (keyGraph q).left k)=r)).card=1 := by
  rcases vertex_partition q r with ⟨v,i,hr⟩ | ⟨c,i,hr⟩ | ⟨j,a,hr⟩
  · have he : r=⟨variableVertex q.val v.val i.val,
        variableVertex_lt q.val v.val i.val v.isLt i.isLt⟩ := Fin.ext hr
    rw [he]
    cases side
    · exact merge_variable_rows q z v i
    · simpa [Equiv.apply_symm_apply] using
        merge_variable_columns q z v ((Cycle.next (occurrences q.val).length).symm i)
  · have he : r=⟨clauseVertex q.val c.val i.val,
        clauseVertex_lt q.val c.val i.val c.isLt i.isLt⟩ := Fin.ext hr
    rw [he]
    cases side
    · exact merge_clause_nodes q z c i false
    · simpa [Equiv.apply_symm_apply] using
        merge_clause_nodes q z c ((Cycle.next (occurrences q.val).length).symm i) true
  · have he : r=⟨xorVertex q.val j.val a.val,
        xorVertex_lt q.val j.val a.val j.isLt a.isLt⟩ := Fin.ext hr
    rw [he]
    exact merge_xor_nodes q z j side a

/-- Independent saved local matchings produce the actual complete
selection of the SAME four-segment original graph. Selected is proved,
never supplied as an input or inferred from cancelled XOR support. -/
theorem merge_selected (q : Input) (z : Joint q) : Selected (keyGraph q) (typedMerge q z) :=
  ⟨merge_node_card q z false,merge_node_card q z true⟩
def reverse (q : Input) (z : Joint q) : Selection (keyGraph q) :=
  ⟨typedMerge q z,merge_selected q z⟩
theorem reverse_capture (q : Input) (s : Selection (keyGraph q)) :
    reverse q (capture q s)=s := Subtype.ext (typed_merge_capture q s)
theorem reverse_selectedIDs (q : Input) (z : Joint q) :
    selectedIDs q (reverse q z)=mergeIDs q z := typed_merge_image q z
theorem reverse_lookup (q : Input) (z : Joint q) (k : KeyID) :
    lookup q (reverse q z) k=decide (k∈mergeIDs q z) := by
  simp only [lookup,reverse_selectedIDs]

private theorem bool_eq_from_true (a b : Bool) (h : a=true ↔ b=true) : a=b := by
  cases a <;> cases b <;> simp_all

theorem reverse_variable (q : Input) (z : Joint q) :
    variableCapture q (reverse q z)=z.remaining.val := by
  funext v i
  apply Prod.ext
  · apply bool_eq_from_true
    simpa [variableCapture,reverse_lookup] using merge_variable_support q z v i false
  · apply bool_eq_from_true
    simpa [variableCapture,reverse_lookup] using merge_variable_support q z v i true
theorem reverse_clause (q : Input) (z : Joint q) (c : Fin q.val.2.length) :
    clauseCapture q (reverse q z) c=(z.clause c).val := by
  funext i
  apply Prod.ext
  · apply bool_eq_from_true
    simpa [clauseCapture,reverse_lookup] using merge_clause_support q z c i false
  · apply bool_eq_from_true
    simpa [clauseCapture,reverse_lookup] using merge_clause_support q z c i true
theorem reverse_vectors (q : Input) (z : Joint q) :
    variableIncoming q (reverse q z)=z.a ∧ clauseIncoming q (reverse q z)=z.b ∧
      variableOutgoing q (reverse q z)=z.c ∧ clauseOutgoing q (reverse q z)=z.d := by
  refine ⟨?_,?_,?_,?_⟩
  all_goals
    funext j
    apply bool_eq_from_true
  · simpa [variableIncoming,reverse_lookup] using merge_connector_support q z j 0
  · simpa [clauseIncoming,reverse_lookup] using merge_connector_support q z j 2
  · simpa [variableOutgoing,reverse_lookup] using merge_connector_support q z j 1
  · simpa [clauseOutgoing,reverse_lookup] using merge_connector_support q z j 3
theorem reverse_xor_word (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    actualXorWord q (reverse q z) j=jointXorWord q z j := by
  obtain ⟨ha,hb,hc,hd⟩ := reverse_vectors q z
  simp only [actualXorWord,jointXorWord,ha,hb,hc,hd]

/-- Canonically ordered matchings are equal when their original edge
choices agree. Row nodup is essential; this is not an endpoint quotient
for the ambient multigraph with its parallel occurrence records. -/
private theorem ordered_edges_ext {A B : Type} [DecidableEq A] [DecidableEq B]
    (es fs : List (A×B)) (hrows : es.map Prod.fst=fs.map Prod.fst)
    (hn : (es.map Prod.fst).Nodup) (hm : ∀ e,e∈es ↔ e∈fs) : es=fs := by
  induction es generalizing fs with
  | nil =>
    cases fs
    · rfl
    · simp at hrows
  | cons a es ih =>
    cases fs with
    | nil => simp at hrows
    | cons b fs =>
      obtain ⟨hr,ht⟩ := List.cons.inj hrows
      have hne := (List.nodup_cons.mp hn).1
      have hab : a=b := by
        have ha := (hm a).mp (by simp)
        rcases List.mem_cons.mp ha with h | h
        · exact h
        · have hv : a.1∈fs.map Prod.fst := List.mem_map.mpr ⟨a,h,rfl⟩
          rw [← ht] at hv
          exact False.elim (hne hv)
      subst b
      have hna : a∉es := by
        intro he
        exact hne (List.mem_map.mpr ⟨a,he,rfl⟩)
      have hnf : a∉fs := by
        intro he
        have hv : a.1∈fs.map Prod.fst := List.mem_map.mpr ⟨a,he,rfl⟩
        rw [← ht] at hv
        exact hne hv
      have htail : ∀ e,e∈es ↔ e∈fs := by
        intro e
        by_cases he : e=a
        · simp [he,hna,hnf]
        · simpa [he] using hm e
      exact congrArg (List.cons a) (ih fs ht (List.nodup_cons.mp hn).2 htail)

theorem reverse_xor_edges (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    xorEdgesCapture q (reverse q z) j=jointXorEdges q z j := by
  have hw := reverse_xor_word q z j
  apply ordered_edges_ext
  · rw [xor_edges_rows,hw,jointXorEdges,jointXorWord,
      (ValiantXor.completion_maps _ _ (List.mem_filter.mp (z.xor j).property).1).1]
  · rw [xor_edges_rows]
    exact ValiantXor.rows_nodup _
  · intro e
    by_cases ha : e∈ValiantXor.template.edges
    · obtain ⟨i,hi⟩ := local_edge_surjective e ha
      rw [← hi,← xor_completion_edges]
      rw [xor_completion_lookup,reverse_lookup]
      simpa using merge_xor_support q z j i
    · have hleft : e∉xorEdgesCapture q (reverse q z) j := by
        intro he
        exact ha (xor_capture_active q (reverse q z) j e he)
      have hright : e∉jointXorEdges q z j := by
        intro he
        exact ha (joint_xor_edges_active q z j e he)
      simp [hleft,hright]

theorem reverse_xor (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    (xorCompletionCapture q (reverse q z) j).val=(z.xor j).val := by
  have hw := reverse_xor_word q z j
  have he := reverse_xor_edges q z j
  have hp : (z.xor j).val∈ValiantXor.actualCompletions (actualXorWord q (reverse q z) j) ∧
      ValiantXor.completionEdges (actualXorWord q (reverse q z) j) (z.xor j).val=
        xorEdgesCapture q (reverse q z) j := by
    constructor
    · simpa only [hw,jointXorWord] using (z.xor j).property
    · simpa only [hw,jointXorEdges] using he.symm
  exact ((Classical.choose_spec (xor_capture_complete q (reverse q z) j)).2 _ hp).symm

theorem joint_ext {q : Input} (z w : Joint q)
    (ha : z.a=w.a) (hb : z.b=w.b) (hc : z.c=w.c) (hd : z.d=w.d)
    (hf : z.remaining.val=w.remaining.val)
    (hg : ∀ i,(z.clause i).val=(w.clause i).val)
    (hh : ∀ j,(z.xor j).val=(w.xor j).val) : z=w := by
  cases z with
  | mk a b c d f g h =>
    cases w with
    | mk a' b' c' d' f' g' h' =>
      cases ha; cases hb; cases hc; cases hd
      have hf' : f=f' := Subtype.ext hf
      have hg' : g=g' := by funext i; exact Subtype.ext (hg i)
      have hh' : h=h' := by funext j; exact Subtype.ext (hh j)
      cases hf'; cases hg'; cases hh'
      rfl
theorem capture_reverse (q : Input) (z : Joint q) : capture q (reverse q z)=z := by
  obtain ⟨ha,hb,hc,hd⟩ := reverse_vectors q z
  exact joint_ext _ z ha hb hc hd (reverse_variable q z) (reverse_clause q z) (reverse_xor q z)

/-- Full equivalence is formed only after both genuine inverse bodies
and the complete reverse row/column Selected producer above. -/
def jointEquiv (q : Input) : Selection (keyGraph q) ≃ Joint q where
  toFun := capture q
  invFun := reverse q
  left_inv := reverse_capture q
  right_inv := capture_reverse q
instance (q : Input) : Fintype (Joint q) := Fintype.ofEquiv (Selection (keyGraph q)) (jointEquiv q)

theorem integer_joint_sum (q : Input) :
    WeightedMatchingInterpolation.integerValue (graph q)=∑ z : Joint q,mergeWeight q z := by
  rw [← (jointEquiv q).sum_comp (mergeWeight q),integer_key_selection_sum]
  exact Finset.sum_congr rfl (fun s _ => (merge_capture_weight q s).symm)


def recordWeight (q : Input) (k : KeyID) : ℤ := if (record q k).2 then -1 else 1
def mergeFactor (q : Input) (z : Joint q) (k : KeyID) : ℤ :=
  if mergeWord q z k then recordWeight q k else 1
theorem merge_weight_list (q : Input) (z : Joint q) :
    mergeWeight q z=((keys q).map (mergeFactor q z)).prod := by
  rw [mergeWeight,mergeIDs,Finset.prod_filter,List.prod_toFinset _ (keys_nodup q)]
  rfl

private theorem flat_map_prod {A B : Type} (xs : List A) (ys : A → List B) (f : B → ℤ) :
    ((xs.flatMap ys).map f).prod=(xs.map (fun a => ((ys a).map f).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [ih]
private theorem range_list_prod (n : ℕ) (f : ℕ → ℤ) :
    ((List.range n).map f).prod=∏ i : Fin n,f i.val := by
  rw [← List.prod_toFinset _ (List.nodup_range (n:=n))]
  have he : (List.range n).toFinset=Finset.range n := by ext i; simp
  rw [he]
  exact Finset.prod_range f
private theorem list_prod_one {A : Type} (xs : List A) (f : A → ℤ) (h : ∀ a∈xs,f a=1) :
    (xs.map f).prod=1 := by
  revert h
  induction xs with
  | nil => intro h; rfl
  | cons a xs ih =>
    intro h
    have ha := h a (by simp)
    have ht : ∀ b∈xs,f b=1 := fun b hb => h b (by simp [hb])
    simp [ha,ih ht]

theorem variable_factor_product (q : Input) (z : Joint q) :
    ((variableKeys q).map (mergeFactor q z)).prod=1 := by
  apply list_prod_one
  intro k hk
  have ht := variableKeys_tag q k hk
  simp [mergeFactor,recordWeight,record,ht,variableRecord]
theorem connector_factor_product (q : Input) (z : Joint q) :
    ((connectorKeys q).map (mergeFactor q z)).prod=1 := by
  apply list_prod_one
  intro k hk
  have ht := connectorKeys_tag q k hk
  have hm : k∈keys q := by
    simp [keys,hk]
  let e : Keys q := ⟨k,List.mem_toFinset.mpr hm⟩
  have hw : recordWeight q k=1 := connector_edge_unit q e ht
  simp [mergeFactor,hw]

private theorem choice_closing_product {n : ℕ} (f : Cycle.Choice n) :
    (∏ i : Fin (n+1),if (f i).2 && decide (i.val=n) then (-1 : ℤ) else 1)=
      Cycle.closingWeight f := by
  calc
    _ = (if (f (Fin.last n)).2 && decide ((Fin.last n).val=n) then (-1 : ℤ) else 1) := by
      apply Finset.prod_eq_single (Fin.last n)
      · intro i _ hi
        have hn : i.val≠n := fun he => hi (Fin.ext he)
        simp [hn]
      · simp
    _ = _ := by simp [Cycle.closingWeight]

theorem clause_factor_pair (q : Input) (z : Joint q) (c : Fin q.val.2.length) (i : Fin (slots q.val)) :
    ([(1,c.val,i.val,false),(1,c.val,i.val,true)].map (mergeFactor q z)).prod=
      if ((z.clause c).val i).2 && decide (i.val=(occurrences q.val).length) then (-1 : ℤ) else 1 := by
  rcases i with ⟨i,hi⟩
  by_cases he : i=(occurrences q.val).length
  · subst i
    cases hb : ((z.clause c).val ⟨(occurrences q.val).length,hi⟩).2 <;>
      simp [mergeFactor,recordWeight,record,mergeWord,c.isLt,hi,hb]
  · cases hb : ((z.clause c).val ⟨i,hi⟩).2 <;>
      simp [mergeFactor,recordWeight,record,mergeWord,c.isLt,hi,hb,he]
theorem clause_block_product (q : Input) (z : Joint q) (c : Fin q.val.2.length) :
    (((List.range (slots q.val)).flatMap
      (fun i => [(1,c.val,i,false),(1,c.val,i,true)])).map (mergeFactor q z)).prod=
      Cycle.closingWeight (z.clause c).val := by
  rw [flat_map_prod,range_list_prod]
  calc
    _ = (∏ i : Fin (slots q.val),
      if ((z.clause c).val i).2 && decide (i.val=(occurrences q.val).length) then (-1 : ℤ) else 1) :=
      Finset.prod_congr rfl (fun i _ => clause_factor_pair q z c i)
    _ = _ := choice_closing_product (z.clause c).val
theorem clause_factor_product (q : Input) (z : Joint q) :
    ((clauseKeys q).map (mergeFactor q z)).prod=
      ∏ c : Fin q.val.2.length,Cycle.closingWeight (z.clause c).val := by
  rw [clauseKeys,flat_map_prod,range_list_prod]
  exact Finset.prod_congr rfl (fun c _ => clause_block_product q z c)

theorem joint_xor_indices_image (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    (jointXorIndices q z j).image localEdge=(jointXorEdges q z j).toFinset := by
  ext e
  simp only [Finset.mem_image,List.mem_toFinset]
  constructor
  · rintro ⟨i,hi,rfl⟩
    exact (Finset.mem_filter.mp hi).2
  · intro he
    obtain ⟨i,hi⟩ := local_edge_surjective e (joint_xor_edges_active q z j e he)
    exact ⟨i,by simp [jointXorIndices,hi,he],hi⟩

theorem xor_factor_record (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) (i : XorIndex) :
    mergeFactor q z (2,j.val,i.val,false)=
      if localEdge i∈jointXorEdges q z j then ValiantXor.matrix (localEdge i).1 (localEdge i).2 else 1 := by
  have hw : recordWeight q (2,j.val,i.val,false)=ValiantXor.matrix (localEdge i).1 (localEdge i).2 :=
    local_record_weight q j i
  simp [mergeFactor,hw,mergeWord,j.isLt,i.isLt,jointXorEdges,jointXorWord]

theorem xor_block_product (q : Input) (z : Joint q) (j : Fin (occurrences q.val).length) :
    (((List.range xorLocal.length).map (fun i => (2,j.val,i,false))).map (mergeFactor q z)).prod=
      ValiantXor.completionWeight (jointXorWord q z j) (z.xor j).val := by
  simp only [List.map_map]
  rw [range_list_prod]
  calc
    _ = (∏ i : XorIndex,if localEdge i∈jointXorEdges q z j
        then ValiantXor.matrix (localEdge i).1 (localEdge i).2 else 1) :=
      Finset.prod_congr rfl (fun i _ => xor_factor_record q z j i)
    _ = (∏ i∈jointXorIndices q z j,ValiantXor.matrix (localEdge i).1 (localEdge i).2) := by
      rw [jointXorIndices,Finset.prod_filter]
    _ = (∏ e∈(jointXorIndices q z j).image localEdge,ValiantXor.matrix e.1 e.2) :=
      (Finset.prod_image (s:=jointXorIndices q z j)
        (f:=fun e=>ValiantXor.matrix e.1 e.2) local_edge_injective.injOn).symm
    _ = (∏ e∈(jointXorEdges q z j).toFinset,ValiantXor.matrix e.1 e.2) := by rw [joint_xor_indices_image]
    _ = ((jointXorEdges q z j).map (fun e => ValiantXor.matrix e.1 e.2)).prod :=
      List.prod_toFinset _ (joint_xor_edges_nodup q z j)
    _ = _ := rfl
theorem xor_factor_product (q : Input) (z : Joint q) :
    ((xorKeys q).map (mergeFactor q z)).prod=
      ∏ j : Fin (occurrences q.val).length,ValiantXor.completionWeight (jointXorWord q z j) (z.xor j).val := by
  rw [xorKeys,flat_map_prod,range_list_prod]
  exact Finset.prod_congr rfl (fun j _ => xor_block_product q z j)

def jointWeight (q : Input) (z : Joint q) : ℤ :=
  (∏ c : Fin q.val.2.length,Cycle.closingWeight (z.clause c).val)*
    (∏ j : Fin (occurrences q.val).length,ValiantXor.completionWeight (jointXorWord q z j) (z.xor j).val)

/-- Whole signed product factorization over the REAL four segments.
Variable/connector factors are proved unit; clause and XOR signs are retained
inside their original complete local matching sums. -/
theorem merge_weight_factorization (q : Input) (z : Joint q) : mergeWeight q z=jointWeight q z := by
  rw [merge_weight_list,keys,List.map_append,List.map_append,List.map_append,
    List.prod_append,List.prod_append,List.prod_append,
    variable_factor_product,clause_factor_product,xor_factor_product,connector_factor_product]
  simp only [one_mul,mul_one,jointWeight]

theorem integer_local_product_sum (q : Input) :
    WeightedMatchingInterpolation.integerValue (graph q)=∑ z : Joint q,jointWeight q z := by
  rw [integer_joint_sum]
  exact Finset.sum_congr rfl (fun z _ => merge_weight_factorization q z)


instance (t : ValiantXor.Word) : Fintype (XorMatching t) :=
  Fintype.ofFinset (ValiantXor.actualCompletions t).toFinset (by
    intro cs
    change cs∈(ValiantXor.actualCompletions t).toFinset ↔ cs∈ValiantXor.actualCompletions t
    exact List.mem_toFinset)
theorem xor_matching_sum (t : ValiantXor.Word) :
    (∑ h : XorMatching t,ValiantXor.completionWeight t h.val)=ValiantXor.actualTensor t := by
  calc
    _ = ∑ cs∈(ValiantXor.actualCompletions t).toFinset,ValiantXor.completionWeight t cs :=
      (Finset.sum_subtype _ (by intro cs; simp) _).symm
    _ = ((ValiantXor.actualCompletions t).map (ValiantXor.completionWeight t)).sum :=
      List.sum_toFinset _ (ValiantXor.actual_completions_nodup t)
    _ = _ := rfl

abbrev ClauseFamily (q : Input) (b d : Source.Bits q) :=
  (i : Fin q.val.2.length) → Cycle.Matching (Source.boundary q i.val b) (Source.boundary q i.val d)
abbrev XorFamily (q : Input) (a b c d : Source.Bits q) :=
  (j : Fin (occurrences q.val).length) → XorMatching ![c j,d j,a j,b j]
abbrev Components (q : Input) (a b c d : Source.Bits q) :=
  Source.RemainingMatching q a c × ClauseFamily q b d × XorFamily q a b c d
abbrev JointSigma (q : Input) :=
  Σ a : Source.Bits q,Σ b : Source.Bits q,Σ c : Source.Bits q,Σ d : Source.Bits q,Components q a b c d

def jointSigmaEquiv (q : Input) : Joint q ≃ JointSigma q where
  toFun z := ⟨z.a,z.b,z.c,z.d,z.remaining,z.clause,z.xor⟩
  invFun p := ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2.1,p.2.2.2.2.2.1,p.2.2.2.2.2.2⟩
  left_inv z := by cases z; rfl
  right_inv p := by rcases p with ⟨a,b,c,d,f,g,h⟩; rfl

theorem clause_family_sum (q : Input) (b d : Source.Bits q) :
    (∑ g : ClauseFamily q b d,∏ i,Cycle.closingWeight (g i).val)=Source.clauses q b d := by
  rw [← Fintype.prod_sum (fun (i : Fin q.val.2.length)
    (g : Cycle.Matching (Source.boundary q i.val b) (Source.boundary q i.val d))=>Cycle.closingWeight g.val)]
  rfl
theorem xor_family_sum (q : Input) (a b c d : Source.Bits q) :
    (∑ h : XorFamily q a b c d,
      ∏ j,ValiantXor.completionWeight ![c j,d j,a j,b j] (h j).val)=Source.allXors q a b c d := by
  rw [← Fintype.prod_sum (fun (j : Fin (occurrences q.val).length)
    (h : XorMatching ![c j,d j,a j,b j])=>ValiantXor.completionWeight ![c j,d j,a j,b j] h.val)]
  simp_rw [xor_matching_sum]
  change (∏ j : Fin (occurrences q.val).length,ValiantXor.actualTensor ![c j,d j,a j,b j])=
    ∏ j : Fin (occurrences q.val).length,ValiantXor.actualTensor ![a j,b j,c j,d j]
  exact Finset.prod_congr rfl (fun j _ => xor_transpose_ports (a j) (b j) (c j) (d j))

/-- Complete independent local signed sums. Neither support restriction
nor a single-matching cancellation is substituted for this finite sum. -/
theorem component_sum (q : Input) (a b c d : Source.Bits q) :
    (∑ _f : Source.RemainingMatching q a c,
      ∑ g : ClauseFamily q b d,∑ h : XorFamily q a b c d,
        (∏ i,Cycle.closingWeight (g i).val)*
          (∏ j,ValiantXor.completionWeight ![c j,d j,a j,b j] (h j).val))=
      Source.allXors q a b c d*(Source.variableTensor q a c*Source.clauses q b d) := by
  have hx (g : ClauseFamily q b d) :
      (∑ h : XorFamily q a b c d,(∏ i,Cycle.closingWeight (g i).val)*
        (∏ j,ValiantXor.completionWeight ![c j,d j,a j,b j] (h j).val))=
          (∏ i,Cycle.closingWeight (g i).val)*Source.allXors q a b c d := by
    rw [← Finset.mul_sum,xor_family_sum]
  have hg :
      (∑ g : ClauseFamily q b d,∑ h : XorFamily q a b c d,
        (∏ i,Cycle.closingWeight (g i).val)*
          (∏ j,ValiantXor.completionWeight ![c j,d j,a j,b j] (h j).val))=
        Source.clauses q b d*Source.allXors q a b c d := by
    simp_rw [hx]
    rw [← Finset.sum_mul,clause_family_sum]
  simp_rw [hg]
  calc
    _ = (∑ _f : Source.RemainingMatching q a c,(1 : ℤ))*
        (Source.clauses q b d*Source.allXors q a b c d) := by
      rw [Finset.sum_mul]
      simp only [one_mul]
    _ = _ := by unfold Source.variableTensor; ring

theorem joint_sigma_sum (q : Input) :
    (∑ z : Joint q,jointWeight q z)=
      ∑ a : Source.Bits q,∑ b : Source.Bits q,∑ c : Source.Bits q,∑ d : Source.Bits q,
        ∑ _f : Source.RemainingMatching q a c,∑ g : ClauseFamily q b d,∑ h : XorFamily q a b c d,
          (∏ i,Cycle.closingWeight (g i).val)*
            (∏ j,ValiantXor.completionWeight ![c j,d j,a j,b j] (h j).val) := by
  rw [← (jointSigmaEquiv q).symm.sum_comp (jointWeight q)]
  simp only [Fintype.sum_sigma,Fintype.sum_prod_type]
  rfl

theorem joint_sum_full_cut (q : Input) :
    (∑ z : Joint q,jointWeight q z)=Source.fullCutValue q := by
  rw [joint_sigma_sum]
  unfold Source.fullCutValue
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro c _
  apply Finset.sum_congr rfl
  intro d _
  exact component_sum q a b c d

/-- Actual whole flattened ordered occurrence graph equals the full cut
contraction. This is a derived signed-sum law, not an input assumption. -/
theorem integer_graph (q : Input) :
    WeightedMatchingInterpolation.integerValue (graph q)=Source.fullCutValue q := by
  rw [integer_local_product_sum,joint_sum_full_cut]


end
end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.MatchingSum
