import Holant.Certificates.TetrahedralOrientation.PhysicalShape

/-! Exact denotation of the six-vertex construction, with one genuine I vertex
and four boundary-first LX binaries joined by native X edges. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

/-- The first two choices are the contracted original ports1/3; the remaining
four choices retain original output order2/4/5/6. -/
def physicalChoices : (Fin 6 → Bool) ≃ (Bool × Bool × (Fin 4 → Bool)) where
  toFun c := (!(c 0),!(c 1),fun j => !(c j.succ.succ))
  invFun q := ![!q.1,!q.2.1,!(q.2.2 0),!(q.2.2 1),!(q.2.2 2),!(q.2.2 3)]
  left_inv c := by funext j; fin_cases j <;> simp
  right_inv q := by
    rcases q with ⟨a,b,y⟩
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · funext j; fin_cases j <;> simp

theorem nativeLeg_edge (L : Binary) (a b : Bool) :
    nativeLeg L a (!b) = L a b := by simp [nativeLeg,Kernel.mul_disequality]

theorem physical_product (s : Orientation) (x y : Fin 4 → Bool) (a b : Bool) :
    (∏ v : Fin 6, terminalLabels s v
      (terminalShape.assignment x (Network.endpointChoiceAssignment (physicalChoices.symm (a,b,y))) v)) =
      ancestor s ![a,y 0,b,y 1,y 2,y 3] * Q0 a b * ∏ j : Fin 4, legs s j (x j) (y j) := by
  have ha : terminalShape.assignment x
      (Network.endpointChoiceAssignment (physicalChoices.symm (a,b,y))) (0 : Fin 6) =
        ![a,y 0,b,y 1,y 2,y 3] := by
    funext i
    fin_cases i <;> simp [terminalShape,NetworkShape.assignment,terminalPortMap,
      Network.endpointChoiceAssignment,physicalChoices,contractOrder]
  simp only [terminalShape,Fin.prod_univ_succ]
  change ancestor s (terminalShape.assignment x
      (Network.endpointChoiceAssignment (physicalChoices.symm (a,b,y))) (0 : Fin 6)) * _ = _
  rw [ha]
  change ancestor s ![a,y 0,b,y 1,y 2,y 3] *
    (Q0 (!a) (!b) * (nativeLeg (legs s 0) (x 0) (!(y 0)) *
      (nativeLeg (legs s 1) (x 1) (!(y 1)) *
        (nativeLeg (legs s 2) (x 2) (!(y 2)) *
          (nativeLeg (legs s 3) (x 3) (!(y 3)) * 1))))) = _
  simp only [nativeLeg_edge,mul_one]
  cases a <;> cases b <;> simp [Q0,Signature.equality,mul_assoc]

theorem terminalNetwork_denote (s : Orientation) : (terminalNetwork s).denote = dressed s := by
  rw [terminalNetwork,Network.denote_disequality]
  funext x
  change (∑ c : Fin 6 → Bool, ∏ v : Fin 6, terminalLabels s v
    (terminalShape.assignment x (Network.endpointChoiceAssignment c) v)) = dressed s x
  rw [← physicalChoices.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  simp_rw [physical_product]
  change (∑ a : Bool, ∑ b : Bool, ∑ y : Fin 4 → Bool,
    ancestor s ![a,y 0,b,y 1,y 2,y 3] * Q0 a b * ∏ j : Fin 4, legs s j (x j) (y j)) = _
  simp [Fintype.sum_bool,Q0,Signature.equality]
  rw [add_comm]
  unfold dressed Signature.coordinateAction
  simp_rw [card_apply,mul_add]
  rw [Finset.sum_add_distrib]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro y hy <;> ring

/-- Only the literal ancestor, I, and the four tetrahedral binary resources occur. -/
def resources (s : Orientation) : SignatureFamily ℂ :=
  {p | p = ⟨6,ancestor s⟩ ∨ p = ⟨2,binarySignature Q0⟩ ∨
    ∃ j : Fin 4, p = ⟨2,binarySignature (nativeLeg (legs s j))⟩}

theorem terminal_realizes (s : Orientation) :
    Gadget.Realizes (resources s) .disequality (dressed s) := by
  have h := Gadget.realizes_network (terminalNetwork s) (resources s) .disequality
    (by intro v; fin_cases v
        · exact Or.inl rfl
        · exact Or.inr (Or.inl rfl)
        · exact Or.inr (Or.inr ⟨0,rfl⟩)
        · exact Or.inr (Or.inr ⟨1,rfl⟩)
        · exact Or.inr (Or.inr ⟨2,rfl⟩)
        · exact Or.inr (Or.inr ⟨3,rfl⟩))
    (by intro e; rfl)
  rwa [terminalNetwork_denote] at h

end
end Holant.Certificates.TetrahedralOrientation
