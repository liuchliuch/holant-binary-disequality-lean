import Holant.Proofs.Hardness.GeneralEOPhaseExtractionCore
import Holant.Proofs.Hardness.GeneralEOPinnedDescentLabels

/-! Actual scaled signed contractions with original labels and native X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionNetwork
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOPhaseExtractionCore (Collinear collinear_scale_iff collinear_reversed_difference)
end C
namespace O
export GeneralEOPinnedDescentOperations (word word_weight cap cap_denote)
end O
namespace L
export GeneralEOPinnedDescentLabels (capLabels cap_exact cap_count cap_native)
end L
namespace LN
export LabelledNetwork (Exact count contract exact_contract count_contract)
end LN
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}

def Signed (B : Network ℂ 2) (t : ℂ) : Prop :=
  B.denote ![false,false]=0 ∧ B.denote ![false,true]=t ∧
  B.denote ![true,false]= -t ∧ B.denote ![true,true]=0

def network (B : Network ℂ 2) (S : Network ℂ (n+2)) (minus : Bool) : Network ℂ n :=
  if minus then O.cap B S else S.contract Signature.disequality

def value (t u v : ℂ) (minus : Bool) : ℂ := if minus then t*(v-u) else u+v

theorem denote (B : Network ℂ 2) (S : Network ℂ (n+2)) (t : ℂ)
    (hB : Signed B t) (minus : Bool) (x : Fin n → Bool) :
    (network B S minus).denote x = value t
      (S.denote (O.word false true x)) (S.denote (O.word true false x)) minus := by
  rcases hB with ⟨h00,h01,h10,h11⟩
  cases minus
  · exact Network.denote_contract_disequality S x
  · change (O.cap B S).denote x=t*(S.denote (O.word true false x)-S.denote (O.word false true x))
    rw [O.cap_denote,h00,h01,h10,h11]
    ring

theorem value_collinear_iff (t u v u' v' : ℂ) (ht : t≠0) (minus : Bool) :
    C.Collinear (value t u v minus) (value t u' v' minus) ↔
      C.Collinear (if minus then u-v else u+v) (if minus then u'-v' else u'+v') := by
  cases minus
  · rfl
  · exact (C.collinear_scale_iff t (v-u) (v'-u') ht).trans
      (C.collinear_reversed_difference u u' v v')

def labels (B : Network ℂ 2) (S : Network ℂ (n+2))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a) (minus : Bool) :
    Labelling (network B S minus).shape s 1 a := by
  cases minus
  · exact LN.contract S SL 0 Signature.disequality
  · exact L.capLabels S SL B BL

theorem exact (G : (i : Fin s) → Signature ℂ (a i.val))
    (B : Network ℂ 2) (S : Network ℂ (n+2))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a)
    (hB : LN.Exact G B BL) (hS : LN.Exact G S SL) (minus : Bool) :
    LN.Exact G (network B S minus) (labels B S BL SL minus) := by
  cases minus
  · exact LN.exact_contract G S SL hS 0 Signature.disequality
  · exact L.cap_exact G S SL hS B BL hB

theorem count (B : Network ℂ 2) (S : Network ℂ (n+2))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a)
    (minus : Bool) (j : Fin s) :
    LN.count (labels B S BL SL minus) j=LN.count SL j+(if minus then LN.count BL j else 0) := by
  cases minus
  · simp only [labels, Bool.false_eq_true, ite_false, add_zero]
    rfl
  · exact (L.cap_count S SL B BL j).trans (add_comm _ _)

theorem native (B : Network ℂ 2) (S : Network ℂ (n+2))
    (hB : ∀e,B.edge e=Signature.disequality)
    (hS : ∀e,S.edge e=Signature.disequality) (minus : Bool) :
    ∀e,(network B S minus).edge e=Signature.disequality := by
  cases minus
  · intro e
    exact Fin.cases rfl (fun e => hS e) e
  · exact L.cap_native S hS B hB

theorem central (B : Network ℂ 2) (S : Network ℂ (n+2)) (t : ℂ)
    (hB : Signed B t) (hS : Signature.CentralSupport S.denote) (minus : Bool) :
    Signature.CentralSupport (network B S minus).denote := by
  intro x hx
  rw [denote B S t hB]
  have h01 : S.denote (O.word false true x)=0 := by
    apply hS
    rw [O.word_weight]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    omega
  have h10 : S.denote (O.word true false x)=0 := by
    apply hS
    rw [O.word_weight]
    simp only [Bool.false_eq_true, ite_false, ite_true]
    omega
  cases minus <;> simp [value,h01,h10]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionNetwork
