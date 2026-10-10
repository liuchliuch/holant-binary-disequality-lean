import Holant.Pauli.ExoticKlein.SixPortCertificate
import Holant.Pauli.ProjectiveDetermination.Ports

/-! Literal finite direction data and six-port card tomography. These are
semantic tensors over Q(i) and ℂ, not projective-line oracle tags. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators

abbrev Direction := Fin 3 × Label × Label
abbrev DirectionTriple := Fin 3 → Option Direction

 def directionTensorOver {K : Type*} [Ring K] (imaginary : K) (d : Direction) : Signature K 4 :=
  fun x => if d.1 = 0 then EOver imaginary d.2.1 (x 0) (x 1)*EOver imaginary d.2.2 (x 2) (x 3)
    else if d.1 = 1 then EOver imaginary d.2.1 (x 0) (x 2)*EOver imaginary d.2.2 (x 1) (x 3)
    else EOver imaginary d.2.1 (x 0) (x 3)*EOver imaginary d.2.2 (x 1) (x 2)

 def directionTensor := directionTensorOver Complex.I
 def gaussianDirection := directionTensorOver gaussianI

 theorem map_gaussianDirection (d : Direction) (x : Fin 4 → Bool) :
    Algebraic.gaussianToComplex (gaussianDirection d x) = directionTensor d x := by
  have hm (a : Label) (u v : Bool) : Algebraic.gaussianToComplex (EOver gaussianI a u v) =
      EOver Complex.I a u v := map_gaussianE a u v
  unfold gaussianDirection directionTensor directionTensorOver
  split_ifs <;> simp only [map_mul,hm]

 def optionDirectionOver {K : Type*} [Ring K] (imaginary : K) : Option Direction → Signature K 4
  | none => 0
  | some d => directionTensorOver imaginary d

 def optionDirection := optionDirectionOver Complex.I
 def gaussianOptionDirection := optionDirectionOver gaussianI

 theorem map_gaussianOptionDirection (d : Option Direction) (x : Fin 4 → Bool) :
    Algebraic.gaussianToComplex (gaussianOptionDirection d x) = optionDirection d x := by
  cases d
  · exact map_zero _
  · exact map_gaussianDirection _ _

 def baseDirection : Direction := (0,0,0)

 def cardDirections (state : DirectionTriple) : Fin 4 → Option Direction :=
  Fin.cons (some baseDirection) state

 theorem direction_count : Fintype.card Direction = 48 := by simp [Direction]
 theorem direction_triple_count : Fintype.card DirectionTriple = 117649 := by
  simp [DirectionTriple,Direction]

 def tail4 (x : Fin 6 → Bool) : Fin 4 → Bool := fun i => x i.succ.succ

/-- The actual dual card on the first two original ports, in their original order. -/
 def baseCard (a : Label) (h : Signature ℂ 6) : Signature ℂ 4 :=
  fun z => ∑ u : Bool, ∑ v : Bool, dual a u v*h (Fin.cons u (Fin.cons v z))

 theorem restore_tail4 (x : Fin 6 → Bool) : Fin.cons (x 0) (Fin.cons (x 1) (tail4 x)) = x := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · refine Fin.cases ?_ (fun j => ?_) j <;> rfl

/-- Exact tomography keeps all four cards, including the zero cards. -/
 theorem base_tomography (h : Signature ℂ 6) (x : Fin 6 → Bool) :
    ∑ a : Label, E a (x 0) (x 1)*baseCard a h (tail4 x) = h x := by
  have he := binary_reconstruction (fun u v => h (Fin.cons u (Fin.cons v (tail4 x)))) (x 0) (x 1)
  rw [restore_tail4] at he
  simpa only [baseCard,Kernel.pair,mul_comm] using he

 theorem exists_nonzero_baseCard (h : Signature ℂ 6) (hn : h ≠ 0) : ∃ a, baseCard a h ≠ 0 := by
  classical
  by_contra ha
  push_neg at ha
  apply hn
  funext x
  have hx := base_tomography h x
  simp only [ha,Pi.zero_apply,mul_zero,Finset.sum_const_zero] at hx
  exact hx.symm

 def normalizedTensor (state : DirectionTriple) (scale : Fin 4 → ℂ) : Signature ℂ 6 :=
  fun x => ∑ i : Fin 4, scale i*E (labelEquiv i) (x 0) (x 1)*
    optionDirection (cardDirections state i) (tail4 x)

/-- If the actual cards have the stated directions/scales, tomography proves
this literal normal form; no reconstructing-host-function premise is used. -/
 theorem normalizedTensor_of_cards (h : Signature ℂ 6) (state : DirectionTriple) (scale : Fin 4 → ℂ)
    (hcards : ∀ i : Fin 4, baseCard (labelEquiv i) h =
      fun z => scale i*optionDirection (cardDirections state i) z) : h = normalizedTensor state scale := by
  funext x
  rw [← base_tomography h x]
  unfold normalizedTensor
  rw [← labelEquiv.sum_comp]
  apply Finset.sum_congr rfl
  intro i hi
  rw [hcards i]
  ring

/-- Computable bit/word coordinates for the literal finite checker matrices. -/
 def bitEquiv : Bool ≃ Fin 2 where
  toFun b := if b then 1 else 0
  invFun i := i = 1
  left_inv b := by cases b <;> rfl
  right_inv i := by fin_cases i <;> rfl

 def wordEquiv (n : ℕ) : (Fin n → Bool) ≃ Fin (2^n) :=
  (Equiv.arrowCongr (Equiv.refl (Fin n)) bitEquiv).trans finFunctionFinEquiv

 def tensorMatrix (state : DirectionTriple) : Fin 64 → LinearCertificate.Row 4 :=
  fun word i => gaussianE (labelEquiv i) ((wordEquiv 6).symm word 0) ((wordEquiv 6).symm word 1)*
    gaussianOptionDirection (cardDirections state i) (tail4 ((wordEquiv 6).symm word))

 theorem tensorMatrix_semantics (state : DirectionTriple) (scale : Fin 4 → ℂ) (word : Fin 64) :
    LinearCertificate.output (tensorMatrix state) scale word =
      normalizedTensor state scale ((wordEquiv 6).symm word) := by
  unfold LinearCertificate.output LinearCertificate.evaluate tensorMatrix normalizedTensor
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_mul,map_gaussianE,map_gaussianOptionDirection]
  ring

end
end Holant.Pauli.ExoticKlein.SixPort
