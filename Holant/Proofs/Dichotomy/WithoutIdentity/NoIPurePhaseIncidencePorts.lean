import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceRegularization
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseIncidenceWeight

/-! Exact modulo-four certificates for the actual signed physical ports.
The transformed row retains each original constant and sign; only its
character name changes, and a zero name becomes a literal pin. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidencePorts
open Holant Holant.Tractable
open NoIPurePhaseRecipeFactor (Port word)
open scoped BigOperators
namespace W
export NoIPurePhaseRecipeFactor (incidence)
export NoIPurePhaseIncidenceWeight (residue sum_zero)
end W
namespace C
export NoIPurePhaseIncidenceCore (bit evenBit rank_two rank_three)
end C
namespace P
export NoIPurePhaseIncidenceRegularization.P (Transform image inputs plus)
def value (j : Fin 8) (x : Fin 3→Bool) : Bool :=
  if h : j=0 then false else NoIPurePhaseIncidenceCore.C.codeSeven x
    ⟨j.val-1,by have hlt:=j.isLt;have hn:=j.pos_iff_ne_zero.mpr h;omega⟩
def linearWord (t : Transform) (x : Fin 3→Bool) : Fin 3→Bool := fun i=>value (inputs t i) x

theorem value_plus (i j : Fin 8) (x : Fin 3→Bool) :
    value (plus i j) x=Bool.xor (value i x) (value j x) := by
  revert i j x
  decide

theorem image_value (t : Transform) (j : Fin 7) (x : Fin 3→Bool) :
    value (image t j) x=NoIPurePhaseIncidenceCore.C.codeSeven (linearWord t x) j := by
  fin_cases j
  · rfl
  · rfl
  · rfl
  · exact value_plus _ _ x
  · exact value_plus _ _ x
  · exact value_plus _ _ x
  · exact (value_plus _ _ x).trans (congrArg₂ Bool.xor (value_plus _ _ x) rfl)
end P
namespace R
def transformed {n : ℕ} (p : Fin n→Port 7) (t : P.Transform) (i : Fin n) : Port 7 :=
  match p i with
  | .inl b=>.inl b
  | .inr (j,s)=>if h : P.image t j=0 then .inl s else
      .inr (⟨(P.image t j).val-1,by have hlt:=(P.image t j).isLt;have hn:=(P.image t j).pos_iff_ne_zero.mpr h;omega⟩,s)

theorem transformed_word {n : ℕ} (p : Fin n→Port 7) (t : P.Transform) (x : Fin 3→Bool) :
    word (transformed p t) (NoIPurePhaseIncidenceCore.C.codeSeven x)=
      word p (NoIPurePhaseIncidenceCore.C.codeSeven (P.linearWord t x)) := by
  funext i
  simp only [word,transformed]
  cases h:p i with
  | inl b=>simp
  | inr v=>
    rcases v with ⟨j,s⟩
    have hv:=P.image_value t j x
    dsimp only
    split_ifs with hz
    · simp [P.value,hz] at hv
      simp [hv]
    · simpa [P.value,hz] using congrArg (fun b=>s ^^ b) hv
end R
namespace A
export NoIPurePhaseIncidenceCore.C (codeThree codeSeven)
end A
namespace Q
export NoIPurePhaseIncidenceRegularization (pattern contribution Corrects translated cases_of_pattern)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192
set_option Elab.async false
variable {n : ℕ}

theorem rank_two (p : Fin n→Port 3)
    (same : ∀x : Fin 2→Bool,weight (word p (A.codeThree x))%4=
      weight (word p (fun _=>false))%4) :
    (∀j,W.residue p j=0) ∨ (∀j,W.residue p j=2) := by
  have h0:=W.sum_zero p (A.codeThree ![true,false]) (same ![true,false])
  have h1:=W.sum_zero p (A.codeThree ![false,true]) (same ![false,true])
  have h2:=W.sum_zero p (A.codeThree ![true,true]) (same ![true,true])
  simp only [A.codeThree,Fin.sum_univ_three,C.bit] at h0 h1 h2
  norm_num at h0 h1 h2
  rcases C.rank_two (W.residue p 0) (W.residue p 1) (W.residue p 2) h0 h1 h2 with h|h
  · left;intro j;fin_cases j <;> simp_all
  · right;intro j;fin_cases j <;> simp_all

theorem rank_three (p : Fin n→Port 7)
    (same : ∀x : Fin 3→Bool,weight (word p (A.codeSeven x))%4=
      weight (word p (fun _=>false))%4) :
    ∃t : ZMod 4,∃u : Fin 3→Bool,∀j,W.residue p j=Q.pattern t u j := by
  have h0:=W.sum_zero p (A.codeSeven ![true,false,false]) (same ![true,false,false])
  have h1:=W.sum_zero p (A.codeSeven ![false,true,false]) (same ![false,true,false])
  have h2:=W.sum_zero p (A.codeSeven ![false,false,true]) (same ![false,false,true])
  have h3:=W.sum_zero p (A.codeSeven ![false,true,true]) (same ![false,true,true])
  have h4:=W.sum_zero p (A.codeSeven ![true,false,true]) (same ![true,false,true])
  have h5:=W.sum_zero p (A.codeSeven ![true,true,false]) (same ![true,true,false])
  have h6:=W.sum_zero p (A.codeSeven ![true,true,true]) (same ![true,true,true])
  norm_num [A.codeSeven,C.bit,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5 h6
  simp only [←add_assoc] at h0 h1 h2 h3 h4 h5 h6
  simpa only [Q.pattern] using C.rank_three (W.residue p) h0 h1 h2 h3 h4 h5 h6

theorem transformed_incidence (p : Fin n→Port 7) (t : P.Transform) (j : Fin 7) :
    W.incidence (R.transformed p t) j=
      ∑k : Fin 7,if P.image t k=j.succ then W.incidence p k else 0 := by
  unfold W.incidence
  have distribute (h : Prop) [Decidable h] (g : Fin n→ℤ) :
      (if h then ∑i,g i else 0)=∑i,if h then g i else 0 := by
    split_ifs <;> simp
  simp_rw [distribute]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  cases hp : p i with
  | inl b=>simp [R.transformed,hp]
  | inr v=>
      rcases v with ⟨k,s⟩
      have he (v : Fin 8) (h : v≠0) : (⟨v.val-1,by omega⟩ : Fin 7)=j ↔ v=j.succ := by
        constructor <;> intro hh <;> apply Fin.ext
        · have hv := congrArg Fin.val hh
          have hn := v.pos_iff_ne_zero.mpr h
          simp only [Fin.val_succ] at hv ⊢
          omega
        · have hv := congrArg Fin.val hh
          simp only [Fin.val_succ] at hv ⊢
          omega
      have hs : j.succ≠(0 : Fin 8) := Fin.succ_ne_zero j
      dsimp only
      rw [Finset.sum_eq_single k]
      · simp only [ite_true]
        by_cases hz : P.image t k=0
        · simp [R.transformed,hp,hz,Ne.symm hs]
        · simp [R.transformed,hp,hz,he _ hz]
      · intro v _ hv
        simp [Ne.symm hv]
      · simp

theorem transformed_residue (p : Fin n→Port 7) (t : P.Transform) (j : Fin 7) :
    W.residue (R.transformed p t) j=Q.contribution (W.residue p) t j := by
  simpa [W.residue,Q.contribution,Int.cast_sum,Int.cast_ite,Int.cast_zero] using
    congrArg (fun z : ℤ=>(z : ZMod 4)) (transformed_incidence p t j)

def rows (p : Fin n→Port 7) (q : Fin 2→P.Transform) : Fin 3→Fin n→Port 7 :=
  Fin.cases p (fun i=>R.transformed p (q i))

theorem rows_zero (p : Fin n→Port 7) (q : Fin 2→P.Transform)
    (corrects : Q.Corrects (W.residue p) q) (j : Fin 7) :
    (∑i : Fin 3,W.incidence (rows p q i) j : ℤ)%4=0 := by
  have hc : (∑i : Fin 3,W.residue (rows p q i) j)=0 := by
    rw [Fin.sum_univ_succ]
    simpa only [rows,Fin.cases_zero,Fin.cases_succ,transformed_residue] using corrects j
  have hz : ((∑i : Fin 3,W.incidence (rows p q i) j : ℤ) : ZMod 4)=0 := by
    simpa only [Int.cast_sum,W.residue] using hc
  exact Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd _ 4).mp hz)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseIncidencePorts
end
