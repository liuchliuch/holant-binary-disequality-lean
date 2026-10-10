import Holant.Proofs.Algorithms.TransformRecognition.AffineNormalForm
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineNormalForm
import Holant.Proofs.Algorithms.TransformRecognition.SparseTransform
import Holant.Proofs.Algorithms.TransformRecognition.ProductVariableLayout
import Mathlib.Data.Finset.Insert


namespace Holant.LocalDrafts.MainChain.TransformRecognition.FiniteBranchEnumeration

/-- All finite vectors, constructed by choosing their head and tail. -/
def vectors {α : Type*} (values : List α) : (n : ℕ) → List (Fin n → α)
  | 0 => [Fin.elim0]
  | n+1 => values.flatMap (fun a => (vectors values n).map (Fin.cons a))

theorem mem_vectors {α : Type*} (values : List α) {n : ℕ} (v : Fin n → α)
    (hv : ∀ i, v i ∈ values) : v ∈ vectors values n := by
  induction n with
  | zero =>
    have he : v=Fin.elim0 := Subsingleton.elim _ _
    simp [vectors,he]
  | succ n ih =>
    apply List.mem_flatMap.mpr
    refine ⟨v 0,hv 0,List.mem_map.mpr ⟨Fin.tail v,ih _ (fun i => hv i.succ),?_⟩⟩
    exact Fin.cons_self_tail v

/-- Powerset generation preserves finite subsets, with harmless duplicate
codes if the underlying universe list repeats elements. -/
def subsets {α : Type*} [DecidableEq α] : List α → List (Finset α)
  | [] => [∅]
  | a::as => subsets as ++ (subsets as).map (insert a)

theorem mem_subsets {α : Type*} [DecidableEq α] (universeList : List α) (S : Finset α)
    (hS : ∀ a ∈ S, a ∈ universeList) : S ∈ subsets universeList := by
  induction universeList generalizing S with
  | nil =>
    have he : S=∅ := Finset.eq_empty_iff_forall_notMem.mpr (by simpa using hS)
    simp [subsets,he]
  | cons a as ih =>
    by_cases ha : a ∈ S
    · have hs : S.erase a ∈ subsets as := ih _ (by
        intro b hb
        have hbS := (Finset.mem_erase.mp hb).2
        rcases List.mem_cons.mp (hS b hbS) with hba | hba
        · exact False.elim ((Finset.mem_erase.mp hb).1 hba)
        · exact hba)
      exact List.mem_append_right _ (List.mem_map.mpr
        ⟨S.erase a,hs,Finset.insert_erase ha⟩)
    · apply List.mem_append_left
      exact ih S (by
        intro b hb
        rcases List.mem_cons.mp (hS b hb) with rfl | hba
        · exact False.elim (ha hb)
        · exact hba)

def residues2 : List (ZMod 2) := [0,1]
def residues4 : List (ZMod 4) := [0,1,2,3]

theorem mem_residues2 (x : ZMod 2) : x ∈ residues2 := by
  exact (by decide : ∀ x : ZMod 2, x ∈ residues2) x

theorem mem_residues4 (x : ZMod 4) : x ∈ residues4 := by
  exact (by decide : ∀ x : ZMod 4, x ∈ residues4) x

def affineEquations (n : ℕ) : List (AffineNormalForm.Equation n) :=
  (vectors residues2 n).flatMap (fun a => residues2.map (fun b => (a,b)))

theorem mem_affineEquations {n : ℕ} (e : AffineNormalForm.Equation n) :
    e ∈ affineEquations n :=
  List.mem_flatMap.mpr ⟨e.1,mem_vectors _ _ (fun _ => mem_residues2 _),
    List.mem_map.mpr ⟨e.2,mem_residues2 _,rfl⟩⟩

def affinePhases (n : ℕ) : List (AffineNormalForm.PhaseCode n) :=
  residues4.flatMap (fun c => (vectors residues4 n).flatMap (fun linear =>
    (vectors (vectors [false,true] n) n).map (fun mixed => (c,linear,mixed))))

theorem mem_affinePhases {n : ℕ} (p : AffineNormalForm.PhaseCode n) :
    p ∈ affinePhases n := by
  apply List.mem_flatMap.mpr
  refine ⟨p.1,mem_residues4 _,List.mem_flatMap.mpr
    ⟨p.2.1,mem_vectors _ _ (fun _ => mem_residues4 _),?_⟩⟩
  apply List.mem_map.mpr
  refine ⟨p.2.2,mem_vectors _ _ (fun i => mem_vectors _ _ (fun j => ?_)),rfl⟩
  cases p.2.2 i j <;> simp

def affineCodes (n : ℕ) : List (AffineNormalForm.Code n) :=
  (subsets (affineEquations n)).flatMap (fun support =>
    (affinePhases n).map (fun phase => (support,phase)))

theorem mem_affineCodes {n : ℕ} (c : AffineNormalForm.Code n) : c ∈ affineCodes n :=
  List.mem_flatMap.mpr ⟨c.1,mem_subsets _ _ (fun _ _ => mem_affineEquations _),
    List.mem_map.mpr ⟨c.2,mem_affinePhases _,rfl⟩⟩

/-- Finite function assignment by explicit updates, for the support-word
indexed affine codes required by L. Defaults are fixed syntax, never roots. -/
def assignments {α β : Type*} [DecidableEq α] (values : List β) (fallback : β) :
    List α → List (α → β)
  | [] => [fun _ => fallback]
  | a::as => values.flatMap (fun b =>
      (assignments values fallback as).map (fun f => Function.update f a b))

theorem assignments_complete {α β : Type*} [DecidableEq α]
    (values : List β) (fallback : β) (domain : List α) (f : α → β)
    (hf : ∀ a ∈ domain, f a ∈ values) :
    ∃ g ∈ assignments values fallback domain, ∀ a ∈ domain, g a=f a := by
  induction domain with
  | nil => exact ⟨fun _ => fallback,by simp [assignments],by simp⟩
  | cons a as ih =>
    obtain ⟨g,hg,hmatch⟩ := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    refine ⟨Function.update g a (f a),List.mem_flatMap.mpr
      ⟨f a,hf a (List.mem_cons_self ..),List.mem_map.mpr ⟨g,hg,rfl⟩⟩,?_⟩
    intro b hb
    by_cases hba : b=a
    · subst b; simp
    · rw [Function.update_of_ne hba]
      exact hmatch b ((List.mem_cons.mp hb).resolve_left hba)

def zeroAffine (n : ℕ) : AffineNormalForm.Code n :=
  (∅,0,(fun _ => 0),(fun _ _ => false))

def localAffineCodes (n : ℕ) : List (LocalAffineNormalForm.Code n) :=
  (subsets (SparseTransform.allWords n)).flatMap (fun support =>
    (assignments (affineCodes n) (zeroAffine n) (SparseTransform.allWords n)).map
      (fun phases => (support,phases)))

theorem mem_localAffineCodes {n : ℕ} (c : LocalAffineNormalForm.Code n) :
    c ∈ localAffineCodes n := by
  obtain ⟨g,hg,hmatch⟩ := assignments_complete (affineCodes n) (zeroAffine n)
    (SparseTransform.allWords n) c.2 (fun _ _ => mem_affineCodes _)
  have he : g=c.2 := funext (fun a => hmatch a (SparseTransform.mem_allWords a))
  apply List.mem_flatMap.mpr
  refine ⟨c.1,mem_subsets _ _ (fun a _ => SparseTransform.mem_allWords a),?_⟩
  exact List.mem_map.mpr ⟨g,hg,by rw [he]⟩


open Holant.LocalDrafts.TetrahedralCompletion.TransformRecognition.ProductNormalForm

def productEdges (n : ℕ) : List (Edge n) :=
  (List.finRange n).flatMap (fun i => (List.finRange n).flatMap (fun j =>
    [((i,j),false),((i,j),true)]))

theorem mem_productEdges {n : ℕ} (e : Edge n) : e ∈ productEdges n := by
  obtain ⟨⟨i,j⟩,b⟩ := e
  apply List.mem_flatMap.mpr
  refine ⟨i,List.mem_finRange i,List.mem_flatMap.mpr ⟨j,List.mem_finRange j,?_⟩⟩
  cases b <;> simp

def productCodes (n : ℕ) : List (Skeleton n) := subsets (productEdges n)

theorem mem_productCodes {n : ℕ} (S : Skeleton n) : S ∈ productCodes n :=
  mem_subsets _ _ (fun e _ => mem_productEdges e)

/-- Heterogeneous arities use dependent finite updates. All labels and their
own row types remain literal; no common padded arity or selected bijection is
assumed. The finite list is computed from the actual arity function. -/
def dependentAssignments {α : Type*} {β : α → Type*} [DecidableEq α]
    (values : ∀ a, List (β a)) (fallback : ∀ a, β a) : List α → List (∀ a, β a)
  | [] => [fallback]
  | a::as => (values a).flatMap (fun b =>
      (dependentAssignments values fallback as).map (fun f => Function.update f a b))

theorem dependentAssignments_complete {α : Type*} {β : α → Type*} [DecidableEq α]
    (values : ∀ a, List (β a)) (fallback : ∀ a, β a) (domain : List α)
    (f : ∀ a, β a) (hf : ∀ a ∈ domain, f a ∈ values a) :
    ∃ g ∈ dependentAssignments values fallback domain, ∀ a ∈ domain, g a=f a := by
  induction domain with
  | nil => exact ⟨fallback,by simp [dependentAssignments],by simp⟩
  | cons a as ih =>
    obtain ⟨g,hg,hmatch⟩ := ih (fun b hb => hf b (List.mem_cons_of_mem _ hb))
    refine ⟨Function.update g a (f a),List.mem_flatMap.mpr
      ⟨f a,hf a (List.mem_cons_self ..),List.mem_map.mpr ⟨g,hg,rfl⟩⟩,?_⟩
    intro b hb
    by_cases hba : b=a
    · subst b; simp
    · rw [Function.update_of_ne hba]
      exact hmatch b ((List.mem_cons.mp hb).resolve_left hba)

variable {s : ℕ} (arity : Fin s → ℕ)

def affineFamilyCodes : List ((i : Fin s) → AffineNormalForm.Code (arity i)) :=
  dependentAssignments (fun i => affineCodes (arity i))
    (fun i => zeroAffine (arity i)) (List.finRange s)

theorem mem_affineFamilyCodes (B : (i : Fin s) → AffineNormalForm.Code (arity i)) :
    B ∈ affineFamilyCodes arity := by
  obtain ⟨g,hg,he⟩ := dependentAssignments_complete
    (fun i => affineCodes (arity i)) (fun i => zeroAffine (arity i)) (List.finRange s)
    B (fun _ _ => mem_affineCodes _)
  have h : g=B := funext (fun i => he i (List.mem_finRange i))
  exact h ▸ hg


def commonAffineCodes : List (((i : Fin s) → AffineNormalForm.Code (arity i)) ×
    AffineNormalForm.Code 2) :=
  (affineFamilyCodes arity).flatMap (fun family => (affineCodes 2).map (fun edge => (family,edge)))

theorem mem_commonAffineCodes
    (B : ((i : Fin s) → AffineNormalForm.Code (arity i)) × AffineNormalForm.Code 2) :
    B ∈ commonAffineCodes arity :=
  List.mem_flatMap.mpr ⟨B.1,mem_affineFamilyCodes arity B.1,
    List.mem_map.mpr ⟨B.2,mem_affineCodes B.2,rfl⟩⟩

def productFamilyCodes : List ((j : ProductVariableLayout.Slot s) →
    Skeleton (ProductVariableLayout.slotArity arity j)) :=
  dependentAssignments (fun j => productCodes (ProductVariableLayout.slotArity arity j))
    (fun _ => ∅) (ProductVariableLayout.slots s)

theorem mem_productFamilyCodes (B : (j : ProductVariableLayout.Slot s) →
    Skeleton (ProductVariableLayout.slotArity arity j)) : B ∈ productFamilyCodes arity := by
  obtain ⟨g,hg,he⟩ := dependentAssignments_complete
    (fun j => productCodes (ProductVariableLayout.slotArity arity j))
    (fun _ => ∅) (ProductVariableLayout.slots s) B (fun _ _ => mem_productCodes _)
  have h : g=B := funext (fun j => he j (ProductVariableLayout.mem_slots j))
  exact h ▸ hg

def localAffineFamilyCodes : List ((j : ProductVariableLayout.Slot s) →
    LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j)) :=
  dependentAssignments
    (fun j => localAffineCodes (ProductVariableLayout.slotArity arity j))
    (fun j => (∅,fun _ => zeroAffine (ProductVariableLayout.slotArity arity j)))
    (ProductVariableLayout.slots s)

theorem mem_localAffineFamilyCodes (B : (j : ProductVariableLayout.Slot s) →
    LocalAffineNormalForm.Code (ProductVariableLayout.slotArity arity j)) :
    B ∈ localAffineFamilyCodes arity := by
  obtain ⟨g,hg,he⟩ := dependentAssignments_complete
    (fun j => localAffineCodes (ProductVariableLayout.slotArity arity j))
    (fun j => (∅,fun _ => zeroAffine (ProductVariableLayout.slotArity arity j)))
    (ProductVariableLayout.slots s) B (fun _ _ => mem_localAffineCodes _)
  have h : g=B := funext (fun j => he j (ProductVariableLayout.mem_slots j))
  exact h ▸ hg

end Holant.LocalDrafts.MainChain.TransformRecognition.FiniteBranchEnumeration
