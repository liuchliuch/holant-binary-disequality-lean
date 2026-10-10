import Holant.Proofs.Hardness.GeneralEOPhaseExtractionNetwork

/-! A supported cross extension shortens Hamming distance. If both cross
extensions vanish, a physical native self-loop retains the coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace C
export GeneralEOPhaseExtractionCore (Collinear noncollinear_through)
end C
namespace O
export GeneralEOPinnedDescentOperations (word word_weight)
end O
namespace LN
export LabelledNetwork (Exact count contract exact_contract count_contract)
end LN
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}

def distance {m : ℕ} (x y : Fin m → Bool) : ℕ := ∑i,if x i=y i then 0 else 1
@[simp] theorem distance_self {m : ℕ} (x : Fin m → Bool) : distance x x=0 := by
  simp [distance]

theorem distance_word (u v u' v' : Bool) (x y : Fin n → Bool) :
    distance (O.word u v x) (O.word u' v' y)=
      (if u=u' then 0 else 1)+(if v=v' then 0 else 1)+distance x y := by
  simp only [distance,O.word,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
  omega

theorem distance_pos {x y : Fin n → Bool} (h : x≠y) : 0<distance x y := by
  classical
  obtain ⟨i,hi⟩ : ∃i,x i≠y i := by
    by_contra hn
    push Not at hn
    exact h (funext hn)
  have hle : (if x i=y i then 0 else 1)≤distance x y := by
    change (if x i=y i then 0 else 1)≤∑j : Fin n,if x j=y j then 0 else 1
    exact Finset.single_le_sum (f := fun j : Fin n => if x j=y j then 0 else 1)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h1 : 1≤distance x y := by simpa only [hi,ite_false] using hle
  omega

def loop (S : Network ℂ (n+2)) : Network ℂ n := S.contract Signature.disequality

theorem loop_denote (S : Network ℂ (n+2)) (x : Fin n → Bool) :
    (loop S).denote x=S.denote (O.word false true x)+S.denote (O.word true false x) :=
  Network.denote_contract_disequality S x

theorem closer_or_lower (S : Network ℂ (n+2)) (x y : Fin n → Bool) (hxy : x≠y)
    (h : ¬C.Collinear (S.denote (O.word false true x))
      (S.denote (O.word true false y))) :
    (∃u v : Fin (n+2) → Bool,
      distance u v < distance (O.word false true x) (O.word true false y) ∧
      ¬C.Collinear (S.denote u) (S.denote v)) ∨
    (¬C.Collinear ((loop S).denote x) ((loop S).denote y) ∧
      (loop S).denote x=S.denote (O.word false true x) ∧
      (loop S).denote y=S.denote (O.word true false y)) := by
  have hd := distance_pos hxy
  by_cases hx : S.denote (O.word true false x)≠0
  · rcases C.noncollinear_through h hx with h'|h'
    · left
      refine ⟨O.word false true x,O.word true false x,?_,h'⟩
      simp only [distance_word,distance_self,Bool.false_eq_true,Bool.true_eq_false,ite_false]
      omega
    · left
      refine ⟨O.word true false x,O.word true false y,?_,h'⟩
      simp only [distance_word,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
      omega
  by_cases hy : S.denote (O.word false true y)≠0
  · rcases C.noncollinear_through h hy with h'|h'
    · left
      refine ⟨O.word false true x,O.word false true y,?_,h'⟩
      simp only [distance_word,Bool.false_eq_true,Bool.true_eq_false,ite_false,ite_true]
      omega
    · left
      refine ⟨O.word false true y,O.word true false y,?_,h'⟩
      simp only [distance_word,distance_self,Bool.false_eq_true,Bool.true_eq_false,ite_false]
      omega
  · have hx0 := not_ne_iff.mp hx
    have hy0 := not_ne_iff.mp hy
    have hlx : (loop S).denote x=S.denote (O.word false true x) := by
      rw [loop_denote,hx0,add_zero]
    have hly : (loop S).denote y=S.denote (O.word true false y) := by
      rw [loop_denote,hy0,zero_add]
    exact Or.inr ⟨by simpa only [hlx,hly] using h,hlx,hly⟩

def labels (S : Network ℂ (n+2)) (L : Labelling S.shape s 1 a) :
    Labelling (loop S).shape s 1 a := LN.contract S L 0 Signature.disequality

theorem exact (G : (i : Fin s) → Signature ℂ (a i.val))
    (S : Network ℂ (n+2)) (L : Labelling S.shape s 1 a) (h : LN.Exact G S L) :
    LN.Exact G (loop S) (labels S L) := LN.exact_contract G S L h 0 Signature.disequality

theorem native (S : Network ℂ (n+2)) (h : ∀e,S.edge e=Signature.disequality) :
    ∀e,(loop S).edge e=Signature.disequality := fun e => Fin.cases rfl (fun e => h e) e

theorem count (S : Network ℂ (n+2)) (L : Labelling S.shape s 1 a) (j : Fin s) :
    LN.count (labels S L) j=LN.count L j := rfl

theorem central (S : Network ℂ (n+2)) (hS : Signature.CentralSupport S.denote) :
    Signature.CentralSupport (loop S).denote := by
  intro x hx
  rw [loop_denote]
  have h01 : S.denote (O.word false true x)=0 := by
    apply hS
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega
  have h10 : S.denote (O.word true false x)=0 := by
    apply hS
    rw [O.word_weight]
    simp only [Bool.false_eq_true,ite_false,ite_true]
    omega
  simp [h01,h10]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionDistance
