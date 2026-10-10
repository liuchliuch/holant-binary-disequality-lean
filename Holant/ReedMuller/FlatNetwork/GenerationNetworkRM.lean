import Holant.ReedMuller.FlatNetwork.GenerationNetworkAttachment
import Holant.ReedMuller.FlatNetwork.GenerationNetworkBasic

/-! A literal RM vertex attached through four I edges implements an arbitrary
weight-four transvection on the current ordinary boundary. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace GenerationNetwork
variable {n m : ℕ}

/-- The source input/output order of the one physical RM vertex. -/
def rmOrder : Fin 8 ≃ Fin 4 ⊕ Fin 4 := rmBoxPorts.symm.trans (finSumFinEquiv (m := 4) (n := 4)).symm

def selectedBoundary (selection : Fin n ≃ Fin 4 ⊕ Fin m) (x : Fin n → Bool) : Fin 4 → Bool :=
  fun i => x (selection.symm (.inl i))

private theorem vector_boxBoundary (selection : Fin n ≃ Fin 4 ⊕ Fin m)
    (a : Fin 4 → Bool) (x : Fin n → Bool) :
    vectorWord (boxBoundary selection rmOrder a x) =
      rmBoxWord (vectorWord a) (vectorWord (selectedBoundary selection x)) := by
  funext i
  change boolEquiv (Sum.elim a (selectedBoundary selection x)
    ((finSumFinEquiv (m := 4) (n := 4)).symm (rmBoxPorts.symm i))) =
    Fin.addCases (vectorWord a) (vectorWord (selectedBoundary selection x)) (rmBoxPorts.symm i)
  generalize hi : rmBoxPorts.symm i = j
  fin_cases j <;> rfl

private theorem ones_four_isotropic : dot (ones 4) (ones 4) = 0 := by decide

def selectedInput (selection : Fin n ≃ Fin 4 ⊕ Fin m) (x : Fin n → Bool) : Fin 4 → Bool :=
  wordVector (transvection (ones 4) (vectorWord (selectedBoundary selection x)))

theorem rmCore_boxBoundary (selection : Fin n ≃ Fin 4 ⊕ Fin m)
    (a : Fin 4 → Bool) (x : Fin n → Bool) :
    rmCore (boxBoundary selection rmOrder a x) =
      if a = selectedInput selection x then 1 else 0 := by
  rw [rmCore, flat_zero_value, vector_boxBoundary, rmBoxWord_mem_iff]
  congr 1
  apply propext
  constructor
  · intro h
    have he : vectorWord a = transvection (ones 4) (vectorWord (selectedBoundary selection x)) := by
      rw [h, transvection_involutive _ ones_four_isotropic]
    rw [← word_vector a, he]
    rfl
  · intro h
    have he : vectorWord a = transvection (ones 4) (vectorWord (selectedBoundary selection x)) := by
      rw [h]
      exact vector_word _
    rw [he, transvection_involutive _ ones_four_isotropic]

/-- One actual RM attachment has exactly one contributing input assignment. -/
theorem denote_attachRM_selected (N : Network ℂ n) (selection : Fin n ≃ Fin 4 ⊕ Fin m)
    (x : Fin n → Bool) :
    (attach N rmCore selection rmOrder).denote x =
      N.denote (inputBoundary selection (selectedInput selection x) x) := by
  rw [denote_attach]
  simp only [rmCore_boxBoundary, mul_ite, mul_one, mul_zero]
  simp

/-- The selected four support indices and the remaining zero indices are
actual original coordinates, not an abstract isometry. -/
def supportIndices (s : BinaryVector n) (hs : binaryWeight s = 4) :
    {i : Fin n // i ∈ wordSupport s} ≃ Fin 4 :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe]
    exact hs)

def zeroIndices (s : BinaryVector n) (hs : binaryWeight s = 4) :
    {i : Fin n // i ∉ wordSupport s} ≃ Fin (n-4) :=
  Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    change n - binaryWeight s = n-4
    rw [hs])

def supportSelection (s : BinaryVector n) (hs : binaryWeight s = 4) :
    Fin n ≃ Fin 4 ⊕ Fin (n-4) :=
  (Equiv.sumCompl (fun i => i ∈ wordSupport s)).symm.trans
    (Equiv.sumCongr (supportIndices s hs) (zeroIndices s hs))

theorem supportSelection_left (s : BinaryVector n) (hs : binaryWeight s = 4) (i : Fin 4) :
    s ((supportSelection s hs).symm (.inl i)) = 1 := by
  change s ((supportIndices s hs).symm i).val = 1
  exact (mem_wordSupport _ _).mp ((supportIndices s hs).symm i).property

theorem supportSelection_right (s : BinaryVector n) (hs : binaryWeight s = 4) (i : Fin (n-4)) :
    s ((supportSelection s hs).symm (.inr i)) = 0 := by
  change s ((zeroIndices s hs).symm i).val = 0
  have hi := ((zeroIndices s hs).symm i).property
  have hne : s ((zeroIndices s hs).symm i).val ≠ 1 := by simpa using hi
  have H : ∀ a : ZMod 2, a ≠ 1 → a = 0 := by decide
  exact H _ hne

theorem dot_supportSelection (s x : BinaryVector n) (hs : binaryWeight s = 4) :
    dot x s = ∑ i : Fin 4, x ((supportSelection s hs).symm (.inl i)) := by
  unfold dot
  rw [← (supportSelection s hs).symm.sum_comp]
  simp only [Fintype.sum_sum_type, supportSelection_left, supportSelection_right,
    mul_one, mul_zero, Finset.sum_const_zero, add_zero]

/-- The input boundary selected by the physical RM relation is exactly the
literal global transvection of the output boundary. -/
theorem inputBoundary_selectedInput (s : BinaryVector n) (hs : binaryWeight s = 4)
    (x : Fin n → Bool) :
    inputBoundary (supportSelection s hs) (selectedInput (supportSelection s hs) x) x =
      wordVector (transvection s (vectorWord x)) := by
  apply funext
  intro i
  let e := supportSelection s hs
  have hi : e.symm (e i) = i := e.symm_apply_apply i
  conv_lhs => rw [← hi]
  conv_rhs => rw [← hi]
  cases hei : e i with
  | inl j =>
    simp only [inputBoundary, e, Equiv.apply_symm_apply, Sum.elim_inl]
    change boolEquiv.symm
      (vectorWord (selectedBoundary e x) j + dot (vectorWord (selectedBoundary e x)) (ones 4) * 1) =
      boolEquiv.symm (vectorWord x (e.symm (.inl j)) + dot (vectorWord x) s * s (e.symm (.inl j)))
    rw [supportSelection_left s hs j]
    congr 2
    rw [dot_supportSelection s (vectorWord x) hs]
    simp [dot, ones, selectedBoundary, vectorWord, e]
  | inr j =>
    simp only [inputBoundary, e, Equiv.apply_symm_apply, Sum.elim_inr]
    change x (e.symm (.inr j)) = boolEquiv.symm
      (vectorWord x (e.symm (.inr j)) + dot (vectorWord x) s * s (e.symm (.inr j)))
    rw [supportSelection_right s hs j]
    simp [vectorWord]

def attachRM (N : Network ℂ n) (s : BinaryVector n) (hs : binaryWeight s = 4) : Network ℂ n :=
  attach N rmCore (supportSelection s hs) rmOrder

@[simp] theorem attachRM_vertices (N : Network ℂ n) (s : BinaryVector n) (hs : binaryWeight s = 4) :
    (attachRM N s hs).shape.vertices = N.shape.vertices+1 := attach_vertices _ _ _ _
@[simp] theorem attachRM_edges (N : Network ℂ n) (s : BinaryVector n) (hs : binaryWeight s = 4) :
    (attachRM N s hs).shape.edges = N.shape.edges+4 := attach_edges _ _ _ _

theorem denote_attachRM (N : Network ℂ n) (s : BinaryVector n) (hs : binaryWeight s = 4)
    (x : Fin n → Bool) :
    (attachRM N s hs).denote x = N.denote (wordVector (transvection s (vectorWord x))) := by
  rw [attachRM, denote_attachRM_selected, inputBoundary_selectedInput]

theorem allowed_attachRM (N : Network ℂ n) (s : BinaryVector n) (hs : binaryWeight s = 4)
    (hN : Allowed N) : Allowed (attachRM N s hs) := by
  constructor
  · intro v
    dsimp only [attachRM, attach, FiniteNetwork.toNetwork]
    cases (Fintype.equivFin (Fin N.shape.vertices ⊕ Unit)).symm v with
    | inl v => exact hN.1 v
    | inr v => exact Or.inr rfl
  · intro e
    dsimp only [attachRM, attach, FiniteNetwork.toNetwork]
    cases (Fintype.equivFin (Fin N.shape.edges ⊕ Fin 4)).symm e with
    | inl e => exact hN.2 e
    | inr e => exact Or.inl rfl

end GenerationNetwork
end
end Holant.ReedMuller.FlatNetwork
