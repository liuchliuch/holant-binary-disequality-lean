import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidencePorts

/-! Three actual copies lift an all-two three-character row to all seven
rank-three character columns. The displayed logical XORs describe only the
semantic code pullback of ordinary signed port substitutions. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoLift
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word incidence)
open scoped BigOperators
namespace A
export NoIPurePhaseIncidenceCore.C (codeThree codeSeven)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n m l : ℕ}

def rename (p : Fin n→Port m) (e : Fin m→Fin l) (i : Fin n) : Port l :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>.inr (e j,s)

theorem rename_word (p : Fin n→Port m) (e : Fin m→Fin l) (z : Fin l→Bool) :
    word (rename p e) z=word p (fun j=>z (e j)) := by
  funext i
  cases h:p i <;> simp [word,rename,h]

theorem rename_incidence (p : Fin n→Port m) (e : Fin m→Fin l) (j : Fin l) :
    incidence (rename p e) j=∑k,if e k=j then incidence p k else 0 := by
  unfold incidence
  have distribute (h : Prop) [Decidable h] (g : Fin n→ℤ) :
      (if h then ∑i,g i else 0)=∑i,if h then g i else 0 := by
    split_ifs <;> simp
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp:p i with
  | inl b=>simp [rename,hp]
  | inr v=>
    rcases v with ⟨k,s⟩
    rw [Finset.sum_eq_single k]
    · simp [rename,hp]
    · intro a _ ha
      simp [Ne.symm ha]
    · simp

def map : Fin 3→Fin 3→Fin 7 := ![![0,3,6],![0,1,5],![0,2,4]]
def logical (x : Fin 3→Bool) : Fin 3→Fin 2→Bool :=
  ![![x 0,x 1^^x 2],![x 0,x 1],![x 0,x 2]]

theorem code_value (x : Fin 3→Bool) (i : Fin 3) :
    (fun j=>A.codeSeven x (map i j))=A.codeThree (logical x i) := by
  revert x i
  decide

def rows (p : Fin n→Port 3) (i : Fin 3) : Fin n→Port 7 := rename p (map i)

theorem rows_word (p : Fin n→Port 3) (x : Fin 3→Bool) (i : Fin 3) :
    word (rows p i) (A.codeSeven x)=word p (A.codeThree (logical x i)) := by
  rw [rows,rename_word,code_value]

theorem residue_two (p : Fin n→Port 3)
    (two : ∀j,(incidence p j : ZMod 4)=2) (j : Fin 7) :
    ((∑i : Fin 3,incidence (rows p i) j : ℤ) : ZMod 4)=2 := by
  simp only [Int.cast_sum,rows,rename_incidence,Int.cast_ite,Int.cast_zero]
  simp_rw [two]
  revert j
  decide

def product (f : Signature AlgebraicComplex n) (p : Fin n→Port 3) : Signature AlgebraicComplex 7 :=
  fun z=>∏i : Fin 3,f (word (rows p i) z)

theorem product_code (f : Signature AlgebraicComplex n) (p : Fin n→Port 3) (x : Fin 3→Bool) :
    product f p (A.codeSeven x)=
      f (word p (A.codeThree ![x 0,x 1^^x 2]))*
      f (word p (A.codeThree ![x 0,x 1]))*
      f (word p (A.codeThree ![x 0,x 2])) := by
  simp only [product,rows_word,Fin.prod_univ_three,logical,Matrix.cons_val_zero,
    Matrix.cons_val_one,Matrix.cons_val_two]
  rfl


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoLift
end
