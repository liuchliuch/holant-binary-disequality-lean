import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4Annihilator
import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset

/-! A fixed four-dimensional exponent box gives polynomially many
annihilator factors. Invalid and desired tuples use zero padding, so the
arithmetic programme need not compare or deduplicate algebraic nodes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Nodes
open scoped BigOperators
namespace A
export GlobalCloseCompletionComplementQ4Annihilator (annihilator degree moment recover)
end A
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K]

def Separated (v : Fin 4→K) (j : Fin 4) : Prop:=
  v j≠0 ∧ ∀m : Fin 4→ℕ,(∃i,i≠j ∧ m i≠0)→v j^(∑i,m i)≠∏i,v i^(m i)

abbrev Box (n : ℕ):=Fin 4→Fin (n+1)
def admissible (n : ℕ) (j : Fin 4) (m : Box n) : Prop:=
  (∑i,(m i).val)=n ∧ ∃i,i≠j ∧ (m i).val≠0
def node (v : Fin 4→K) (j : Fin 4) (n : ℕ) (m : Box n) : K:=by
  classical
  exact if admissible n j m then ∏i,v i^(m i).val else 0

theorem separation (v : Fin 4→K) (j : Fin 4) (h : Separated v j) (n : ℕ) (m : Box n) :
    v j^n≠node v j n m := by
  classical
  unfold node
  split_ifs with good
  · obtain ⟨total,foreign⟩:=good
    simpa only [total] using h.2 (fun i=>(m i).val) foreign
  · exact pow_ne_zero _ h.1

theorem card_box (n : ℕ) : Fintype.card (Box n)=(n+1)^4 := by
  simp [Box,Fintype.card_fun]
theorem degree (v : Fin 4→K) (j : Fin 4) (n : ℕ) :
    (A.annihilator (node v j n)).natDegree=(n+1)^4 := by
  rw [A.degree,card_box]

theorem recover (v : Fin 4→K) (j : Fin 4) (h : Separated v j)
    (n : ℕ) (coefficients : Box n→K) (answer : K) :
    A.moment (A.annihilator (node v j n))
      (fun k=>answer*(v j^n)^k+∑i,coefficients i*(node v j n i)^k) /
      (v j^n*∏i,(v j^n-node v j n i))=answer :=
  A.recover (node v j n) coefficients (v j^n) answer (pow_ne_zero _ h.1) (separation v j h n)

theorem of_dominant (v : Fin 4→ℂ) (j : Fin 4) (nonzero : v j≠0)
    (dominant : ∀i,i≠j→‖v i‖<‖v j‖) : Separated v j := by
  classical
  refine ⟨nonzero,?_⟩
  intro m foreign equal
  have productNonzero : (∏i,v i^(m i))≠0:=equal ▸ pow_ne_zero _ nonzero
  have each (i : Fin 4) : v i^(m i)≠0:=Finset.prod_ne_zero_iff.mp productNonzero i (Finset.mem_univ i)
  have positive (i : Fin 4) (_ : i∈Finset.univ) : 0<‖v i‖^(m i) := by
    rw [←norm_pow]
    exact norm_pos_iff.mpr (each i)
  have weak (i : Fin 4) (_ : i∈Finset.univ) : ‖v i‖^(m i)≤‖v j‖^(m i) := by
    apply pow_le_pow_left₀ (norm_nonneg _)
    by_cases same : i=j
    · exact same ▸ le_rfl
    · exact (dominant i same).le
  have strict : ∃i∈Finset.univ,‖v i‖^(m i)<‖v j‖^(m i) := by
    obtain ⟨i,ij,mi⟩:=foreign
    exact ⟨i,Finset.mem_univ i,pow_lt_pow_left₀ (dominant i ij) (norm_nonneg _) mi⟩
  have inequality:=Finset.prod_lt_prod₀ positive weak strict
  rw [Finset.prod_pow_eq_pow_sum] at inequality
  have normEquality:=congrArg (fun z : ℂ=>‖z‖) equal
  rw [norm_pow,norm_prod] at normEquality
  simp_rw [norm_pow] at normEquality
  exact inequality.ne normEquality.symm

theorem example_separated : Separated (![3,-1,2,0] : Fin 4→ℂ) 0 := by
  apply of_dominant
  · norm_num
  · intro i hi
    fin_cases i
    · exact False.elim (hi rfl)
    all_goals norm_num


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Nodes
end
