import Holant.Proofs.Hardness.GeneralEOPhaseExtractionNetwork

/-! A physical two-port arity descent retaining a non-real phase difference.
This is the distance-two base of MWX Lemma 47 after common 011 coordinates
are moved to the prefix. No auxiliary coefficient is assumed nonzero. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionStep
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOPhaseExtractionCore (Collinear noncollinear_signed_contraction noncollinear_nonzero)
end C
namespace N
export GeneralEOPhaseExtractionNetwork (Signed network value denote value_collinear_iff
  labels exact native central count)
end N
namespace R
export GeneralEOPinnedDescentNetwork (reboundary reboundaryLabels reboundary_denote)
end R
namespace LN
export LabelledNetwork (Exact count)
end LN
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}

def triple (u v w : Bool) (x : Fin n → Bool) : Fin (n+3) → Bool :=
  Fin.cons u (Fin.cons v (Fin.cons w x))

inductive Pair where
  | firstSecond | firstThird | secondThird
  deriving DecidableEq, Repr, Fintype

def perm : Pair → Equiv.Perm (Fin (n+3))
  | .firstSecond => Equiv.refl _
  | .firstThird => Equiv.swap 1 2
  | .secondThird => (Equiv.swap 0 1).trans (Equiv.swap 1 2)

theorem triple_swap_tail (u v w : Bool) (x : Fin n → Bool) :
    triple u v w x ∘ (Equiv.swap 1 2) = triple u w v x := by
  change Matrix.vecCons u (Matrix.vecCons v (Matrix.vecCons w x)) ∘
    (Equiv.swap (0 : Fin (n+2)).succ (1 : Fin (n+2)).succ) = _
  rw [←Matrix.cons_swap, Matrix.cons_cons_comp_swap_zero_one]
  rfl

theorem triple_swap_head (u v w : Bool) (x : Fin n → Bool) :
    triple u v w x ∘ (Equiv.swap 0 1) = triple v u w x := by
  exact Matrix.cons_cons_comp_swap_zero_one u v (Fin.cons w x)

def leftWord (x : Fin n → Bool) : Pair → Fin (n+3) → Bool
  | .firstSecond => triple false true true x
  | .firstThird => triple false true true x
  | .secondThird => triple true false true x

def rightWord (x : Fin n → Bool) : Pair → Fin (n+3) → Bool
  | .firstSecond => triple true false true x
  | .firstThird => triple true true false x
  | .secondThird => triple true true false x

theorem perm_left (x : Fin n → Bool) (p : Pair) :
    triple false true true x ∘ perm p=leftWord x p := by
  cases p
  · rfl
  · exact triple_swap_tail false true true x
  · change (triple false true true x ∘ Equiv.swap 1 2) ∘ Equiv.swap 0 1=_
    rw [triple_swap_tail, triple_swap_head]
    rfl

theorem perm_right (x : Fin n → Bool) (p : Pair) :
    triple true false true x ∘ perm p=rightWord x p := by
  cases p
  · rfl
  · exact triple_swap_tail true false true x
  · change (triple true false true x ∘ Equiv.swap 1 2) ∘ Equiv.swap 0 1=_
    rw [triple_swap_tail, triple_swap_head]
    rfl

def network (B : Network ℂ 2) (S : Network ℂ (n+3)) (p : Pair) (minus : Bool) :
    Network ℂ (n+1) := N.network B (R.reboundary S (perm p)) minus

theorem denote (B : Network ℂ 2) (S : Network ℂ (n+3)) (t : ℂ)
    (hB : N.Signed B t) (p : Pair) (minus : Bool) (x : Fin n → Bool) :
    (network B S p minus).denote (Fin.cons true x)=
      N.value t (S.denote (leftWord x p)) (S.denote (rightWord x p)) minus := by
  rw [network, N.denote B _ t hB, R.reboundary_denote]
  simp only [Tensor.reindex_apply]
  change N.value t (S.denote (triple false true true x ∘ perm p))
    (S.denote (triple true false true x ∘ perm p)) minus=_
  rw [perm_left,perm_right]

theorem exists_noncollinear (B : Network ℂ 2) (S : Network ℂ (n+3)) (t : ℂ)
    (ht : t≠0) (hB : N.Signed B t) (x y : Fin n → Bool)
    (h : ¬C.Collinear (S.denote (triple false true true x))
      (S.denote (triple false true true y))) :
    ∃p : Pair, ∃minus : Bool,
      ¬C.Collinear ((network B S p minus).denote (Fin.cons true x))
        ((network B S p minus).denote (Fin.cons true y)) := by
  have hc := C.noncollinear_signed_contraction
    (S.denote (triple false true true x)) (S.denote (triple false true true y))
    (S.denote (triple true false true x)) (S.denote (triple true false true y))
    (S.denote (triple true true false x)) (S.denote (triple true true false y)) h
  have lift (p : Pair) (minus : Bool)
      (hh : ¬C.Collinear
        (if minus then S.denote (leftWord x p)-S.denote (rightWord x p)
          else S.denote (leftWord x p)+S.denote (rightWord x p))
        (if minus then S.denote (leftWord y p)-S.denote (rightWord y p)
          else S.denote (leftWord y p)+S.denote (rightWord y p))) :
      ¬C.Collinear ((network B S p minus).denote (Fin.cons true x))
        ((network B S p minus).denote (Fin.cons true y)) := by
    rw [denote B S t hB, denote B S t hB]
    exact fun hh' => hh ((N.value_collinear_iff t _ _ _ _ ht minus).mp hh')
  rcases hc with h|h|h|h|h|h
  · exact ⟨.firstSecond,false,lift .firstSecond false h⟩
  · exact ⟨.firstSecond,true,lift .firstSecond true h⟩
  · exact ⟨.firstThird,false,lift .firstThird false h⟩
  · exact ⟨.firstThird,true,lift .firstThird true h⟩
  · exact ⟨.secondThird,false,lift .secondThird false h⟩
  · exact ⟨.secondThird,true,lift .secondThird true h⟩

def labels (B : Network ℂ 2) (S : Network ℂ (n+3))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a)
    (p : Pair) (minus : Bool) : Labelling (network B S p minus).shape s 1 a :=
  N.labels B _ BL (R.reboundaryLabels S SL (perm p)) minus

theorem exact (G : (i : Fin s) → Signature ℂ (a i.val))
    (B : Network ℂ 2) (S : Network ℂ (n+3))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a)
    (hB : LN.Exact G B BL) (hS : LN.Exact G S SL) (p : Pair) (minus : Bool) :
    LN.Exact G (network B S p minus) (labels B S BL SL p minus) :=
  N.exact G B (R.reboundary S (perm p)) BL (R.reboundaryLabels S SL (perm p)) hB hS minus

theorem native (B : Network ℂ 2) (S : Network ℂ (n+3))
    (hB : ∀e,B.edge e=Signature.disequality)
    (hS : ∀e,S.edge e=Signature.disequality) (p : Pair) (minus : Bool) :
    ∀e,(network B S p minus).edge e=Signature.disequality :=
  N.native B (R.reboundary S (perm p)) hB hS minus

theorem count (B : Network ℂ 2) (S : Network ℂ (n+3))
    (BL : Labelling B.shape s 1 a) (SL : Labelling S.shape s 1 a)
    (p : Pair) (minus : Bool) (j : Fin s) :
    LN.count (labels B S BL SL p minus) j=LN.count SL j+(if minus then LN.count BL j else 0) :=
  N.count B _ BL _ minus j

theorem central (B : Network ℂ 2) (S : Network ℂ (n+3)) (t : ℂ)
    (hB : N.Signed B t) (hS : Signature.CentralSupport S.denote) (p : Pair) (minus : Bool) :
    Signature.CentralSupport (network B S p minus).denote := by
  apply N.central B _ t hB
  intro x hx
  rw [R.reboundary_denote]
  apply hS
  have hw : weight (x ∘ perm p)=weight x := Equiv.sum_comp (perm p) (fun b => if x b then 1 else 0)
  change 2*weight (x ∘ perm p)≠n+3
  rw [hw]
  exact hx

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionStep
