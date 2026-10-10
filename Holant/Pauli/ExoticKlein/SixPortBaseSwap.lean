import Holant.Pauli.ExoticKlein.SixPortOrbitWitness

/-! One additional physical symmetry: swap the two original base ports.
The exotic transpose convention exchanges the y/z card slots and negates
both corresponding scales. No arbitrary permutation of Bell coordinates is used. -/
namespace Holant.Pauli.ExoticKlein.SixPort
noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

def basePortSwap : Equiv.Perm (Fin 6) := Equiv.swap 0 1

def baseSwapState (state : DirectionTriple) : DirectionTriple := ![state 0,state 2,state 1]
def baseSwapScale (scale : Fin 4 → ℂ) : Fin 4 → ℂ := ![scale 0,scale 1,-scale 3,-scale 2]

theorem baseSwapState_involutive : Function.Involutive baseSwapState := by
  intro state
  funext i
  fin_cases i <;> rfl

theorem baseSwap_admissible (state : DirectionTriple) (scale : Fin 4 → ℂ) (ha : Admissible state scale) :
    Admissible (baseSwapState state) (baseSwapScale scale) := by
  intro i
  fin_cases i
  · exact ha 0
  · exact ha 1
  · have hh := ha 3
    change (if (state 2).isSome then -scale 3 ≠ 0 else -scale 3 = 0)
    change (if (state 2).isSome then scale 3 ≠ 0 else scale 3 = 0) at hh
    simpa only [neg_ne_zero,neg_eq_zero] using hh
  · have hh := ha 2
    change (if (state 1).isSome then -scale 2 ≠ 0 else -scale 2 = 0)
    change (if (state 1).isSome then scale 2 ≠ 0 else scale 2 = 0) at hh
    simpa only [neg_ne_zero,neg_eq_zero] using hh

theorem baseSwap_normalized (state : DirectionTriple) (scale : Fin 4 → ℂ) :
    Tensor.reindex basePortSwap (normalizedTensor state scale) =
      normalizedTensor (baseSwapState state) (baseSwapScale scale) := by
  funext x
  have ht : tail4 (fun i => x (basePortSwap i)) = tail4 x := by
    funext i
    fin_cases i <;> apply congrArg x <;> decide
  have h0 : basePortSwap 0 = 1 := by decide
  have h1 : basePortSwap 1 = 0 := by decide
  have htrans (a : Label) : E a (x 1) (x 0) =
      transposeScalar a*E (theta a) (x 0) (x 1) :=
    congrFun (congrFun (transpose_E a) (x 0)) (x 1)
  simp only [Tensor.reindex,normalizedTensor,Fin.sum_univ_succ,Fin.sum_univ_zero,
    cardDirections,Fin.cons_zero,Fin.cons_succ,labelEquiv,Equiv.coe_fn_mk,Fin.isValue,
    baseSwapState,baseSwapScale,h0,h1,ht,Matrix.cons_val_zero,Matrix.cons_val_succ]
  rw [htrans 0,htrans xLabel,htrans yLabel,htrans zLabel]
  simp only [theta_zero,theta_x,theta_y,theta_z,transposeScalar,xLabel,yLabel,zLabel]
  norm_num [theta]
  simp only [two_zmod]
  ring

theorem solved_of_baseSwap (state : DirectionTriple) (hs : Solved (baseSwapState state)) : Solved state := by
  intro scale ha hsafe hn
  have hp := hs (baseSwapScale scale) (baseSwap_admissible state scale ha)
  have hs' := allPhysicalSafe_reindex basePortSwap _ hsafe
  have hn' := reindex_ne_zero basePortSwap _ hn
  rw [baseSwap_normalized] at hs' hn'
  have he := hp hs' hn'
  rw [←baseSwap_normalized] at he
  exact isProduct_of_reindex basePortSwap _ he

theorem baseSwap_solved_iff (state : DirectionTriple) : Solved (baseSwapState state) ↔ Solved state := by
  constructor
  · exact solved_of_baseSwap state
  · intro hs
    apply solved_of_baseSwap
    simpa only [baseSwapState_involutive state] using hs

end
end Holant.Pauli.ExoticKlein.SixPort
