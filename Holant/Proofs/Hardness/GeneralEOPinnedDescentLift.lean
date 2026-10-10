import Holant.Proofs.Hardness.GeneralEOPinnedDescentSource

/-! An ambient algebraic-complex source graph lifts to the unchanged original
coefficient field on exactly the same incidence shape. The lift is derived
from actual labels and native edges; no coefficient-membership oracle is an
input. This lets larger structural inductions use either scalar type. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentLift
open Holant Holant.Complexity Holant.Algebraic Holant.Tractable
open FixedGadgetSubstitution
namespace P
export GeneralEOPinnedDescentPalette (arity palette pinned original original_value)
end P
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalField)
end O
namespace OT
export Holant.LocalDrafts.BinaryInterpolation.OriginalTables (castSignature)
end OT
set_option backward.isDefEq.respectTransparency false
variable {n s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance fieldAlgebra : Algebra ℚ (O.originalField G) := (O.originalField G).algebra'

private theorem cast_apply {K : Type} [Field K] {m k : ℕ} (h : m=k)
    (f : Signature K m) (x : Fin k → Bool) :
    OT.castSignature h f x=f (fun i => x (Fin.cast h i)) := by
  subst k
  rfl

theorem palette_value (i : Fin (s+1)) (x : Fin (P.arity (s:=s) (a:=a) i.val) → Bool) :
    (P.pinned G i x : AlgebraicComplex)=P.palette G i x := by
  unfold P.pinned P.palette
  by_cases hi : i.val<s
  · simp only [dite_eq_left hi,cast_apply]
    rfl
  · simp only [dite_eq_right hi,cast_apply,GeneralEOPinnedDescentNetwork.directed01]
    split_ifs <;> rfl

variable (S : Network AlgebraicComplex n)
variable (L : Labelling S.shape (s+1) 1 (P.arity (s:=s) (a:=a)))

/-- Same vertices, same local arities, same incidence permutation, same edges. -/
def lift : Network (O.originalField G) n :=
  L.sourceNetwork (P.pinned G) (fun _ : Fin 1 => Signature.disequality)

def labels : Labelling (lift G S L).shape (s+1) 1 (P.arity (s:=s) (a:=a)) := L

private theorem exact_cast {K : Type} {m k : ℕ} (h : m=k) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨k,fun x => f (fun i => x (Fin.cast h i))⟩ := by
  subst k
  rfl

theorem exact : LabelledNetwork.Exact (P.pinned G) (lift G S L) (labels G S L) := by
  intro v
  exact exact_cast (L.vertex_arity v) (P.pinned G (L.vertex v))

theorem native : ∀e,(lift G S L).edge e=Signature.disequality := fun _ => rfl

variable (he : LabelledNetwork.Exact (P.palette G) S L)
variable (hn : ∀e,S.edge e=Signature.disequality)

private theorem apply_exact {K : Type} {m k : ℕ} (f : Signature K m) (g : Signature K k)
    (h : (⟨m,f⟩ : AnySignature K)=⟨k,g⟩) (hk : m=k) (x : Fin k → Bool) :
    f (fun i => x (Fin.cast hk i))=g x := by
  cases h
  rfl

include he hn in
/-- The ambient graph is recovered exactly, including every nullary scalar. -/
theorem map_lift : (lift G S L).map (O.originalField G).subtype=S := by
  unfold Network.map lift Labelling.sourceNetwork
  congr 1
  · funext v x
    change (P.pinned G (L.vertex v) (fun i => x (Fin.cast (L.vertex_arity v) i)) : AlgebraicComplex)=S.vertex v x
    rw [palette_value]
    exact apply_exact _ _ (he v) (L.vertex_arity v) x
  · funext e u v
    rw [hn e]
    cases u <;> cases v <;> rfl

include he hn in
theorem denote_lift (x : Fin n → Bool) :
    ((lift G S L).denote x : AlgebraicComplex)=S.denote x := by
  change (O.originalField G).subtype ((lift G S L).denote x)=_
  rw [←Network.denote_map (O.originalField G).subtype,map_lift G S L he hn]

include he hn in
theorem nonzero (x : Fin n → Bool) : (lift G S L).denote x≠0 ↔ S.denote x≠0 := by
  have h := denote_lift G S L he hn x
  constructor
  · intro hx hz
    apply hx
    apply Subtype.ext
    exact h.trans hz
  · intro hx hz
    apply hx
    rw [←h,hz]
    rfl

include he hn in
theorem zero (x : Fin n → Bool) : (lift G S L).denote x=0 ↔ S.denote x=0 := by
  exact not_iff_not.mp (nonzero G S L he hn x)

include he hn in
theorem central (hc : Signature.CentralSupport S.denote) :
    Signature.CentralSupport (lift G S L).denote := by
  intro x hx
  exact (zero G S L he hn x).mpr (hc x hx)

theorem graph_counts : (lift G S L).shape.vertices=S.shape.vertices ∧
    (lift G S L).shape.edges=S.shape.edges := ⟨rfl,rfl⟩

theorem occurrences (j : Fin (s+1)) :
    LabelledNetwork.count (labels G S L) j=LabelledNetwork.count L j := rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPinnedDescentLift
