import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.ValiantXor
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Cycle
open scoped BigOperators

abbrev Vertex (n : ℕ) := Fin (n+1)
abbrev Choice (n : ℕ) := Vertex n → Bool × Bool
def bit (b : Bool) : ℕ := if b then 1 else 0
abbrev next (n : ℕ) := finRotate (n+1)

/-- The column equation is written at `next i`; the rotation is a bijection,
so it checks every column exactly once. The first/second bits select the
diagonal/forward edge, respectively. -/
def Valid {n : ℕ} (a b : Vertex n → Bool) (f : Choice n) : Prop :=
  (∀ i,bit (f i).1+bit (f i).2+bit (a i)=1) ∧
  (∀ i,bit (f (next n i)).1+bit (f i).2+bit (b (next n i))=1)

instance {n : ℕ} (a b : Vertex n → Bool) (f : Choice n) : Decidable (Valid a b f) := by
  unfold Valid
  infer_instance

abbrev Matching {n : ℕ} (a b : Vertex n → Bool) := {f : Choice n // Valid a b f}
instance {n : ℕ} (a b : Vertex n → Bool) : Fintype (Matching a b) := by
  unfold Matching
  infer_instance

theorem rotate_constant {n : ℕ} {A : Type} (f : Vertex n → A)
    (h : ∀ i,f (next n i)=f i) : ∀ i,f i=f 0 := by
  have aux : ∀ k (hk : k<n+1),f ⟨k,hk⟩=f 0 := by
    intro k
    induction k with
    | zero => intro hk; rfl
    | succ k ih =>
      intro hk
      have hp : k<n := by omega
      have hs := h ⟨k,by omega⟩
      rw [finRotate_of_lt hp] at hs
      exact hs.trans (ih (by omega))
  intro i
  exact aux i.val i.isLt

def canonical {n : ℕ} (t : Vertex n → Bool) (b : Bool) : Choice n :=
  fun i => (!(t i || b),b)
def Allowed {n : ℕ} (t : Vertex n → Bool) (b : Bool) : Prop :=
  b=false ∨ ∀ i,t i=false
instance {n : ℕ} (t : Vertex n → Bool) (b : Bool) : Decidable (Allowed t b) := by
  unfold Allowed
  infer_instance

theorem paired_shift_constant {n : ℕ} (t : Vertex n → Bool) (f : Choice n)
    (h : Valid t t f) : ∀ i,(f i).2=(f 0).2 := by
  apply rotate_constant (fun i => (f i).2)
  intro i
  have hr := h.1 (next n i)
  have hc := h.2 i
  cases hs : (f i).2 <;> cases ht : (f (next n i)).2 <;>
    simp only [bit,hs,ht,Bool.false_eq_true,if_false,if_true] at hr hc ⊢ <;> omega

theorem paired_classification {n : ℕ} (t : Vertex n → Bool) (f : Choice n) :
    Valid t t f ↔ Allowed t (f 0).2 ∧ f=canonical t (f 0).2 := by
  constructor
  · intro h
    have hs := paired_shift_constant t f h
    have hd (i : Vertex n) : (f i).1=!(t i || (f 0).2) := by
      have hr := h.1 i
      rw [hs i] at hr
      cases ht : t i <;> cases hb : (f 0).2 <;> cases hx : (f i).1 <;>
        simp [bit,ht,hb,hx] at hr ⊢
    have ha : Allowed t (f 0).2 := by
      cases hb : (f 0).2 with
      | false => exact Or.inl rfl
      | true =>
        right
        intro i
        have hr := h.1 i
        rw [hs i,hb] at hr
        cases ht : t i <;> simp [bit,ht] at hr ⊢
    refine ⟨ha,?_⟩
    funext i
    exact Prod.ext (hd i) (hs i)
  · rintro ⟨ha,he⟩
    rw [he]
    rcases ha with hb | ht
    · rw [hb]
      constructor
      · intro i
        cases hti : t i <;> simp [canonical,bit,hti]
      · intro i
        cases hti : t (next n i) <;> simp [next,finRotate_apply] at hti <;> simp [canonical,bit,hti]
    · cases (f 0).2 <;> simp [canonical,ht,Valid,bit]

theorem canonical_valid {n : ℕ} (t : Vertex n → Bool) (b : Bool)
    (h : Allowed t b) : Valid t t (canonical t b) := by
  apply (paired_classification t (canonical t b)).mpr
  exact ⟨h,rfl⟩

/-- The equivalence is used ONLY for finite-sum semantics, never as a
serialization or physical graph program. -/
def pairedEquiv {n : ℕ} (t : Vertex n → Bool) :
    Matching t t ≃ {b : Bool // Allowed t b} where
  toFun f := ⟨(f.val 0).2,((paired_classification t f.val).mp f.property).1⟩
  invFun b := ⟨canonical t b.val,canonical_valid t b.val b.property⟩
  left_inv f := Subtype.ext (((paired_classification t f.val).mp f.property).2.symm)
  right_inv b := rfl

def closingWeight {n : ℕ} (f : Choice n) : ℤ :=
  if (f (Fin.last n)).2 then -1 else 1
def edgeWeight {n : ℕ} (f : Choice n) (i : Vertex n) : ℤ :=
  if (f i).2 && decide (i=Fin.last n) then -1 else 1

/-- The sign is the product of the ACTUAL selected cycle-edge weights.
All diagonal occurrences and all other cycle occurrences have weight one. -/
theorem weight_product {n : ℕ} (f : Choice n) :
    (∏ i : Vertex n,edgeWeight f i)=closingWeight f := by
  rw [Finset.prod_eq_single (Fin.last n)]
  · simp [edgeWeight,closingWeight]
  · intro i _ hi
    simp [edgeWeight,hi]
  · simp

noncomputable def fullTensor {n : ℕ} (a b : Vertex n → Bool) : ℤ :=
  ∑ f : Matching a b,closingWeight f.val

/-- Full row/column occupations are allowed by the semantics above. The
following paired restriction is proved from their actual matching choices. -/
theorem paired_tensor {n : ℕ} (t : Vertex n → Bool) :
    fullTensor t t=if ∃ i,t i=true then 1 else 0 := by
  classical
  unfold fullTensor
  rw [← (pairedEquiv t).symm.sum_comp (fun f => closingWeight f.val)]
  change (∑ b : {b : Bool // Allowed t b},if b.val then (-1 : ℤ) else 1)=_
  let good : Finset Bool := Finset.univ.filter (Allowed t)
  have hgood (b : Bool) : b∈good ↔ Allowed t b := by simp [good]
  rw [← Finset.sum_subtype good hgood (fun b => if b then (-1 : ℤ) else 1)]
  rw [Finset.sum_filter,Fintype.sum_bool]
  by_cases ht : ∃ i,t i=true
  · obtain ⟨i,hi⟩ := ht
    have hn : ¬∀ j,t j=false := by
      intro h
      have hk := h i
      rw [hi] at hk
      exact Bool.noConfusion hk
    simp [Allowed,hn,show (∃ j,t j=true) from ⟨i,hi⟩]
  · have hall : ∀ i,t i=false := by
      intro i
      cases h : t i with
      | false => rfl
      | true => exact False.elim (ht ⟨i,h⟩)
    simp [Allowed,hall,ht]

abbrev emptyBoundary (n : ℕ) : Vertex n → Bool := fun _ => false
abbrev VariableMatching (n : ℕ) := Matching (emptyBoundary n) (emptyBoundary n)

def variableEquiv (n : ℕ) : VariableMatching n ≃ Bool :=
  (pairedEquiv (emptyBoundary n)).trans {
    toFun := Subtype.val
    invFun := fun b => ⟨b,Or.inr (fun _ => rfl)⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }

theorem variable_diagonal (n : ℕ) (f : VariableMatching n) (i : Vertex n) :
    (f.val i).1=!(variableEquiv n f) := by
  have h := ((paired_classification (emptyBoundary n) f.val).mp f.property).2
  rw [h]
  rfl
theorem variable_forward (n : ℕ) (f : VariableMatching n) (i : Vertex n) :
    (f.val i).2=variableEquiv n f := paired_shift_constant _ _ f.property i

/-- A positive literal marks the diagonal edge, a negative literal marks
the forward edge. The marked edge is selected exactly when that literal is
FALSE. Repeated occurrences use different physical cycle slots. -/
def marked {n : ℕ} (f : VariableMatching n) (i : Vertex n) (positive : Bool) : Bool :=
  if positive then (f.val i).1 else (f.val i).2
theorem marked_false {n : ℕ} (f : VariableMatching n) (i : Vertex n) (positive : Bool) :
    marked f i positive=!(variableEquiv n f == positive) := by
  cases positive <;> simp [marked,variable_diagonal,variable_forward]

theorem unused_variable_count (n : ℕ) : Fintype.card (VariableMatching n)=2 := by
  rw [Fintype.card_congr (variableEquiv n)]
  rfl

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.GlobalSignedMatching.Cycle
