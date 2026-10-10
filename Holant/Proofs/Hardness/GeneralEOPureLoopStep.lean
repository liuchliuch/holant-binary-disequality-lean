import Holant.Proofs.Hardness.GeneralEOPureLoopCore

/-! A native X self-loop deletes one actual oriented pair. A forced endpoint
kills exactly one summand, and the original failed restriction is recovered
from the smaller restriction by a fixed unary coordinate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopStep
open Holant Holant.Tractable Holant.Complexity FixedGadgetSubstitution
open GeneralEOPureLoopCore
namespace N
export GeneralEOPinnedDescentNetwork (reboundary reboundary_denote reboundaryLabels)
end N
namespace E
export GeneralEOCentralHoleCoordinates (reboundary_word reboundary_central)
end E
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace D
export GeneralEODEQProducerStep (loop loop_denote loop_central)
end D
set_option backward.isDefEq.respectTransparency false
variable {n m s : ℕ} {a : ℕ → ℕ}

def normalized (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) : Network AlgebraicComplex (m*2+2) :=
  N.reboundary T (normalize p e).symm

def output (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) : Network AlgebraicComplex (m*2) :=
  D.loop (normalized T p e)

def labels (T : Network AlgebraicComplex n) (L : Labelling T.shape s 1 a)
    (p : OrientedPerfectPairing n) (e : Fin (m+1) ≃ Fin p.count) :
    Labelling (output T p e).shape s 1 a :=
  LabelledNetwork.contract (normalized T p e)
    (N.reboundaryLabels T L (normalize p e).symm) 0 Signature.disequality

theorem exact (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (T : Network AlgebraicComplex n) (L : Labelling T.shape s 1 a)
    (h : LabelledNetwork.Exact G T L) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) :
    LabelledNetwork.Exact G (output T p e) (labels T L p e) := h

theorem native (T : Network AlgebraicComplex n) (h : ∀k,T.edge k=Signature.disequality)
    (p : OrientedPerfectPairing n) (e : Fin (m+1) ≃ Fin p.count) :
    ∀k,(output T p e).edge k=Signature.disequality :=
  fun k => Fin.cases rfl (fun k => h k) k

theorem central (T : Network AlgebraicComplex n) (h : Signature.CentralSupport T.denote)
    (p : OrientedPerfectPairing n) (e : Fin (m+1) ≃ Fin p.count) :
    Signature.CentralSupport (output T p e).denote :=
  D.loop_central _ (E.reboundary_central T (normalize p e) h)

def orientation (c side : Bool) : Bool := if side then !c else c

theorem forced_normalized (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (c side : Bool)
    (hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=c) :
    ∀x,(normalized T p e).denote x≠0 → x ((expanded m).ports ((0 : Fin (m+1)),side))=c := by
  intro x hx
  rw [normalized,N.reboundary_denote,Tensor.reindex_apply] at hx
  have hh := hf _ hx
  change x ((normalize p e).symm (p.ports (e 0,side)))=c at hh
  simpa only [←normalize_port p e 0 side,Equiv.symm_apply_apply] using hh

theorem opposite_zero (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (c side : Bool)
    (hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=c) (x : Fin (m*2) → Bool) :
    (normalized T p e).denote (O.word (!(orientation c side)) (orientation c side) x)=0 := by
  by_contra hh
  have h := forced_normalized T p e c side hf _ hh
  cases side <;> cases c <;> simp [orientation,O.word] at h

theorem output_slice (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (c side : Bool)
    (hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=c) (x : Fin (m*2) → Bool) :
    (output T p e).denote x=(normalized T p e).denote
      (O.word (orientation c side) (!(orientation c side)) x) := by
  have hz := opposite_zero T p e c side hf x
  rw [output,D.loop_denote]
  cases hb : orientation c side <;> simp_all

theorem normalized_restrict (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (z : Fin p.count → Bool) :
    (normalized T p e).denote (O.word (z (e 0)) (!(z (e 0)))
      ((standard m).word (fun i => z (e i.succ)))) = p.restrict T.denote z := by
  have hh := E.reboundary_word T (normalize p e) (p.word z)
  rw [word_normalize,expanded_word] at hh
  exact hh

theorem recover (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (c side : Bool)
    (hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=c) (z : Fin p.count → Bool) :
    p.restrict T.denote z = (if z (e 0)=orientation c side then 1 else 0) *
      (standard m).restrict (output T p e).denote (fun i => z (e i.succ)) := by
  rw [←normalized_restrict T p e z]
  by_cases hb : z (e 0)=orientation c side
  · simp only [hb,ite_true,one_mul,OrientedPerfectPairing.restrict]
    exact (output_slice T p e c side hf _).symm
  · have hz : z (e 0)=!(orientation c side) := by
      cases h₁ : z (e 0) <;> cases h₂ : orientation c side <;> simp_all
    rw [if_neg hb,zero_mul,hz,Bool.not_not]
    exact opposite_zero T p e c side hf _

theorem bad (T : Network AlgebraicComplex n) (p : OrientedPerfectPairing n)
    (e : Fin (m+1) ≃ Fin p.count) (c side : Bool)
    (hf : ∀x,T.denote x≠0 → x (p.ports (e 0,side))=c)
    (C : EOClass) (hb : ¬C.Holds (p.restrict T.denote)) :
    ¬C.Holds ((standard m).restrict (output T p e).denote) := by
  intro hh
  apply hb
  exact class_recover C _ _ (fun i => e i.succ) (e 0) (orientation c side)
    (recover T p e c side hf) hh

theorem arity_lt (p : OrientedPerfectPairing n) (e : Fin (m+1) ≃ Fin p.count) : m*2<n := by
  have he := Fintype.card_congr e
  have hp := Fintype.card_congr p.ports
  simp only [Fintype.card_fin,Fintype.card_prod,Fintype.card_bool] at he hp
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPureLoopStep
