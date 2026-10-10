import Holant.Pauli.ProjectiveDetermination.Line
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Physical two-port deletion and assignment reconstruction. The remaining
ports are their literal subtype, retaining all original port identities. -/
namespace Holant.Pauli.ProjectiveDetermination
noncomputable section
open scoped BigOperators
variable {ι β : Type*} [DecidableEq ι]

abbrev Rest (r s : ι) := {i : ι // i ≠ r ∧ i ≠ s}

def fill (r s : ι) (a b : β) (z : Rest r s → β) (i : ι) : β :=
  if hr : i = r then a else if hs : i = s then b else z ⟨i,hr,hs⟩

@[simp] theorem fill_left (r s : ι) (a b : β) (z : Rest r s → β) : fill r s a b z r = a := by simp [fill]
@[simp] theorem fill_right (r s : ι) (hne : r ≠ s) (a b : β) (z : Rest r s → β) : fill r s a b z s = b := by
  simp [fill,Ne.symm hne]
@[simp] theorem fill_rest (r s : ι) (a b : β) (z : Rest r s → β) (i : Rest r s) : fill r s a b z i = z i := by
  simp [fill,i.property.1,i.property.2]

def assignmentEquiv (r s : ι) (hne : r ≠ s) : (ι → β) ≃ β × β × (Rest r s → β) where
  toFun x := (x r,x s,fun i => x i)
  invFun p := fill r s p.1 p.2.1 p.2.2
  left_inv x := by
    funext i
    by_cases hr : i = r
    · simp [fill,hr]
    · by_cases hs : i = s
      · simp [fill,hr,hs,hne,Ne.symm hne]
      · simp [fill,hr,hs,hne,Ne.symm hne]
  right_inv p := by
    rcases p with ⟨a,b,z⟩
    simp only [fill_left,fill_right r s hne]
    congr 2
    funext i
    exact fill_rest r s a b z i

variable [Fintype ι]

theorem sum_assignments [Fintype β] (r s : ι) (hne : r ≠ s) (f : (ι → β) → ℂ) :
    ∑ x, f x = ∑ a, ∑ b, ∑ z : Rest r s → β, f (fill r s a b z) := by
  have h := Fintype.sum_equiv (assignmentEquiv (β := β) r s hne) f
    (fun p => f (fill r s p.1 p.2.1 p.2.2)) (by intro x; exact congrArg f ((assignmentEquiv (β := β) r s hne).left_inv x).symm)
  simpa only [Fintype.sum_prod_type] using h

theorem prod_ports (r s : ι) (hne : r ≠ s) (f : ι → ℂ) :
    ∏ i, f i = f r*f s*∏ i : Rest r s, f i := by
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ r)]
  rw [← Finset.mul_prod_erase (Finset.univ.erase r) f (a := s) (by simp [Ne.symm hne])]
  rw [Finset.prod_subtype ((Finset.univ.erase r).erase s)
    (by intro i; simp only [Finset.mem_erase,Finset.mem_univ,and_true]; exact and_comm) f]
  exact (mul_assoc _ _ _).symm

end
end Holant.Pauli.ProjectiveDetermination
