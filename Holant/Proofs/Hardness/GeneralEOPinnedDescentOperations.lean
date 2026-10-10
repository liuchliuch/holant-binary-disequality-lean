import Holant.Proofs.Hardness.GeneralEOPinnedDescentNetwork

/-! The two physical operations used by Lemma 50: complementary prefix
pinning and a cap extracted from a second actual copy with balanced paired
pins. No signed edge or normalized binary is introduced. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentOperations
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace N
export GeneralEOPinnedDescentNetwork
  (reboundary reboundary_denote reboundaryLabels plugLabels plug_exact plug_count
   bank bank_denote bankLabels bank_exact bank_count pairing directed01)
end N
namespace P
export Holant.ReedMuller.TwoChart.NetworkPlug
  (plug vertices edges denote_plug_disequality native_edges)
end P
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n s : ℕ} {a : ℕ → ℕ}

def word (u v : Bool) (x : Fin n → Bool) : Fin (n+2) → Bool := Fin.cons u (Fin.cons v x)

theorem word_weight (u v : Bool) (x : Fin n → Bool) :
    weight (word u v x)=(if u then 1 else 0)+(if v then 1 else 0)+weight x := by
  simp only [weight,word,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,Nat.add_assoc]

def front : Fin (n+2) ≃ Fin (2+n) := finCongr (Nat.add_comm n 2)
def rotate : Equiv.Perm (Fin (n+2)) :=
  (front (n:=n)).trans (finSumFinEquiv.symm.trans ((Equiv.sumComm _ _).trans finSumFinEquiv))

theorem front_word (u v : Bool) (x : Fin n → Bool) :
    (fun i : Fin (n+2) => (Fin.addCases (![u,v] : Fin 2 → Bool) x : Fin (2+n) → Bool) (front i))=word u v x := by
  funext i
  refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun i => ?_) i) i
  · simp [front,word,Fin.addCases]
    rfl
  · simp [front,word,Fin.addCases]
    rfl
  · simp [front,word,Fin.addCases]
    congr 1

theorem rotate_word (u v : Bool) (x : Fin n → Bool) :
    (fun i : Fin (n+2) => (Fin.addCases x (![u,v] : Fin 2 → Bool) : Fin (n+2) → Bool) (rotate i))=word u v x := by
  rw [←front_word u v x]
  funext i
  change (Fin.addCases x (![u,v] : Fin 2 → Bool) : Fin (n+2) → Bool)
    (finSumFinEquiv ((Equiv.sumComm _ _) (finSumFinEquiv.symm (front i))))=_
  obtain ⟨q,hq⟩ := (@finSumFinEquiv 2 n).surjective (front i)
  rw [←hq]
  cases q <;> simp

private theorem sum_cons {m : ℕ} (F : (Fin (m+1)→Bool)→K) :
    (∑x,F x)=∑b : Bool,∑x : Fin m→Bool,F (Fin.cons b x) := by
  classical
  let : Fintype (Bool×(Fin m→Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
  rw [←(Fin.consEquiv (fun _ : Fin (m+1)=>Bool)).sum_comp,Fintype.sum_prod_type]
  rfl

private theorem sum_two_bits (W : (Fin 2→Bool)→K) :
    (∑x,W x)=W ![false,false]+W ![false,true]+W ![true,false]+W ![true,true] := by
  rw [sum_cons]
  simp_rw [sum_cons]
  simp only [Fintype.sum_bool,Finset.univ_unique,Finset.sum_singleton]
  change (W ![true,true]+W ![true,false])+(W ![false,true]+W ![false,false])=_
  ac_rfl

/-- Attach an actual binary network across the first two source ports. -/
def cap (B : Network K 2) (S : Network K (n+2)) : Network K n :=
  P.plug B (N.reboundary S front) (fun _ => Signature.disequality)

theorem cap_denote (B : Network K 2) (S : Network K (n+2)) (x : Fin n → Bool) :
    (cap B S).denote x=
      B.denote ![true,true]*S.denote (word false false x)+
      B.denote ![false,true]*S.denote (word true false x)+
      B.denote ![true,false]*S.denote (word false true x)+
      B.denote ![false,false]*S.denote (word true true x) := by
  rw [cap,P.denote_plug_disequality,N.reboundary_denote]
  simp only [Tensor.reindex_apply]
  rw [sum_two_bits]
  rw [front_word,front_word,front_word,front_word]
  have hn (u v : Bool) : (fun i => !((![u,v] : Fin 2 → Bool) i))=![!u,!v] := by
    funext i
    fin_cases i <;> rfl
  simp only [hn,Bool.not_false,Bool.not_true]
  ring

/-- Pin all n tail ports of a second copy, retaining its two prefix ports. -/
def extracted (S : Network K (n+2)) (w : Fin n → Bool) (hw : 2*weight w=n) : Network K 2 :=
  P.plug (N.bank w hw) (N.reboundary S rotate) (fun _ => Signature.disequality)

theorem extracted_denote (S : Network K (n+2)) (w : Fin n → Bool) (hw : 2*weight w=n)
    (u v : Bool) : (extracted S w hw).denote ![u,v]=S.denote (word u v w) := by
  classical
  rw [extracted,P.denote_plug_disequality]
  simp only [N.bank_denote]
  have hn (y : Fin n → Bool) : (fun i => !(y i))=(fun i => !(w i)) ↔ y=w := by
    constructor
    · intro h
      funext i
      have hi := congrFun h i
      cases hy : y i <;> cases hw : w i <;> simp_all
    · rintro rfl
      rfl
  simp only [hn,ite_mul,one_mul,zero_mul,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
  rw [N.reboundary_denote,Tensor.reindex_apply,rotate_word]

/-- One literal paired pin suffices for either complementary prefix. -/
def pinned (S : Network K (n+2)) (u : Bool) : Network K n :=
  cap (N.bank (![u,!u] : Fin 2 → Bool) (by cases u <;> decide)) S

theorem pinned_denote (S : Network K (n+2)) (u : Bool) (x : Fin n → Bool) :
    (pinned S u).denote x=S.denote (word u (!u) x) := by
  classical
  rw [pinned,cap_denote]
  simp only [N.bank_denote]
  have hn (v t : Bool) : (fun i => !((![v,t] : Fin 2 → Bool) i))=![!v,!t] := by
    funext i
    fin_cases i <;> rfl
  simp only [hn]
  cases u <;> norm_num

/-- Cancellation is repaired by the unnormalized second-copy cap. -/
def signed (S : Network K (n+2)) (w : Fin n → Bool) (hw : 2*weight w=n) : Network K n :=
  cap (extracted S w hw) S

theorem signed_denote (S : Network K (n+2)) (he : Signature.CentralSupport S.denote)
    (w : Fin n → Bool) (hw : 2*weight w=n)
    (hc : S.denote (word true false w)+S.denote (word false true w)=0)
    (x : Fin n → Bool) :
    (signed S w hw).denote x=
      S.denote (word true false w)*(S.denote (word false true x)-S.denote (word true false x)) := by
  have h00 : S.denote (word false false w)=0 := he _ (by rw [word_weight]; simp only [Bool.false_eq_true,ite_false,zero_add]; omega)
  have h11 : S.denote (word true true w)=0 := he _ (by rw [word_weight]; simp only [ite_true]; omega)
  have h01 : S.denote (word false true w)= -S.denote (word true false w) := by linear_combination hc
  rw [signed,cap_denote]
  simp only [extracted_denote,h00,h11,h01,zero_mul,zero_add,add_zero]
  ring

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentOperations
