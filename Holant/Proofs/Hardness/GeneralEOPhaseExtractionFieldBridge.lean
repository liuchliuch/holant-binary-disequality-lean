import Holant.Proofs.Hardness.GeneralEOPhaseExtractionInduction
import Holant.NetworkAlgebra

/-! Complex phase decisions return an actual original-field
graph by its exact labels; no field equality or free coefficient is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionFieldBridge
open Holant Holant.Complexity FixedGadgetSubstitution
namespace LN
export LabelledNetwork (Exact count)
end LN
namespace I
export GeneralEOPhaseExtractionInduction (Phase nonars_quaternary)
end I
namespace N
export GeneralEOPhaseExtractionNetwork (Signed)
end N
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s n : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val)) (φ : K →+* ℂ)

def family (i : Fin s) : Signature ℂ (arity i.val) := fun x => φ (G i x)

private def mapAny (z : AnySignature K) : AnySignature ℂ := ⟨z.1,fun x => φ (z.2 x)⟩

theorem map_exact (T : Network K n) (TL : Labelling T.shape s 1 arity)
    (hT : LN.Exact G T TL) : LN.Exact (family G φ) (T.map φ) TL :=
  fun v => congrArg (mapAny φ) (hT v)

theorem map_native (T : Network K n) (hT : ∀e,T.edge e=Signature.disequality) :
    ∀e,(T.map φ).edge e=Signature.disequality := by
  intro e
  funext u v
  change φ (T.edge e u v)=_
  rw [hT e]
  cases u <;> cases v <;> simp [Signature.disequality]

theorem map_central (T : Network K n) (hT : Signature.CentralSupport T.denote) :
    Signature.CentralSupport (T.map φ).denote := by
  intro x hx
  rw [Network.denote_map,hT x hx,map_zero]

def rebuild (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity) : Network K n :=
  QL.sourceNetwork G (fun _ : Fin 1 => Signature.disequality)

def labels (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity) :
    Labelling (rebuild G Q QL).shape s 1 arity := QL

omit [Field K] in
private theorem exact_cast {m k : ℕ} (h : m=k) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨k,fun x => f (fun i => x (Fin.cast h i))⟩ := by
  subst k
  rfl

theorem rebuild_exact (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity) :
    LN.Exact G (rebuild G Q QL) (labels G Q QL) := by
  intro v
  exact exact_cast (QL.vertex_arity v) (G (QL.vertex v))

theorem rebuild_native (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity) :
    ∀e,(rebuild G Q QL).edge e=Signature.disequality := fun _ => rfl

private theorem apply_exact {m k : ℕ} (f : Signature ℂ m) (g : Signature ℂ k)
    (h : (⟨m,f⟩ : AnySignature ℂ)=⟨k,g⟩) (hk : m=k) (x : Fin k → Bool) :
    f (fun i => x (Fin.cast hk i))=g x := by
  cases h
  rfl

theorem map_rebuild (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity)
    (hQ : LN.Exact (family G φ) Q QL) (hN : ∀e,Q.edge e=Signature.disequality) :
    (rebuild G Q QL).map φ=Q := by
  unfold Network.map rebuild Labelling.sourceNetwork
  congr 1
  · funext v x
    exact apply_exact _ _ (hQ v) (QL.vertex_arity v) x
  · funext e u v
    rw [hN e]
    cases u <;> cases v <;> simp [Signature.disequality]

theorem rebuild_central (Q : Network ℂ n) (QL : Labelling Q.shape s 1 arity)
    (hQ : LN.Exact (family G φ) Q QL) (hN : ∀e,Q.edge e=Signature.disequality)
    (hE : Signature.CentralSupport Q.denote) : Signature.CentralSupport (rebuild G Q QL).denote := by
  intro x hx
  apply φ.injective
  rw [map_zero,←Network.denote_map φ,map_rebuild G φ Q QL hQ hN]
  exact hE x hx

theorem nonars_quaternary (B : Network K 2) (BL : Labelling B.shape s 1 arity)
    (hBL : LN.Exact G B BL) (hBN : ∀e,B.edge e=Signature.disequality)
    (t : ℂ) (ht : t≠0) (hBt : N.Signed (B.map φ) t)
    (T : Network K n) (TL : Labelling T.shape s 1 arity)
    (hL : LN.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hE : Signature.CentralSupport T.denote)
    (hSign : GeneralEOPhaseExtractionSigns.Sign (T.map φ).denote)
    (hA : ¬GeneralEOARSBoundary.ARSUpToScale (T.map φ).denote) :
    ∃ (Q : Network K 4) (QL : Labelling Q.shape s 1 arity),
      LN.Exact G Q QL ∧ (∀e,Q.edge e=Signature.disequality) ∧
      Signature.CentralSupport Q.denote ∧ I.Phase (Q.map φ).denote ∧
      GeneralEOPhaseExtractionSigns.Sign (Q.map φ).denote := by
  obtain ⟨Q,QL,hQL,hQN,hQE,hQP,hTrace⟩ := I.nonars_quaternary
    (family G φ) (B.map φ) BL t (map_exact G φ B BL hBL) (map_native φ B hBN) ht hBt
    (T.map φ) TL (map_exact G φ T TL hL) (map_native φ T hN)
    (map_central φ T hE) hSign hA
  refine ⟨rebuild G Q QL,labels G Q QL,rebuild_exact G Q QL,rebuild_native G Q QL,
    rebuild_central G φ Q QL hQL hQN hQE,?_⟩
  rw [map_rebuild G φ Q QL hQL hQN]
  exact ⟨hQP,GeneralEOPhaseExtractionReach.preserves_sign (B.map φ) t hBt hTrace hSign⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionFieldBridge
