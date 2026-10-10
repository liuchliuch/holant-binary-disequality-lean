import Holant.Proofs.Hardness.GeneralEOAffinePlaneChain

/-! Literal retained-family labels for the crossed quaternary chain. The
compiled macro uses only one selected original label and native X edges. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChainLabels
open Holant Holant.Complexity FixedGadgetSubstitution
namespace C
export GeneralEOAffinePlaneChain (series seriesOrder copies literal)
end C
namespace L
export LabelledNetwork (tensor reindex contract Exact exact_tensor exact_reindex exact_contract)
end L
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {s : ℕ} {a : ℕ→ℕ}

/-- Every added edge receives the unique native-X label. -/
def series (N M : Network K 4) (l : Labelling N.shape s 1 a)
    (r : Labelling M.shape s 1 a) : Labelling (C.series N M).shape s 1 a :=
  L.contract _ (L.contract _ (L.reindex _ (L.tensor N M l r) C.seriesOrder)
    0 Signature.disequality) 0 Signature.disequality

theorem series_exact (G : (i : Fin s)→Signature K (a i.val))
    (N M : Network K 4) (l : Labelling N.shape s 1 a) (r : Labelling M.shape s 1 a)
    (hl : L.Exact G N l) (hr : L.Exact G M r) :
    L.Exact G (C.series N M) (series N M l r) :=
  L.exact_contract G _ _
    (L.exact_contract G _ _
      (L.exact_reindex _ _ G (L.exact_tensor N M l r G hl hr) C.seriesOrder)
      0 Signature.disequality) 0 Signature.disequality

def copies (N : Network K 4) (l : Labelling N.shape s 1 a) :
    (k : ℕ)→Labelling (C.copies N k).shape s 1 a
  | 0 => l
  | k+1 => series (C.copies N k) N (copies N l k) l

theorem copies_exact (G : (i : Fin s)→Signature K (a i.val))
    (N : Network K 4) (l : Labelling N.shape s 1 a)
    (hl : L.Exact G N l) (k : ℕ) : L.Exact G (C.copies N k) (copies N l k) := by
  induction k with
  | zero => exact hl
  | succ k ih => exact series_exact G _ _ _ _ ih hl

variable (G : (i : Fin s)→Signature K (a i.val)) (j : Fin s)
variable (M : Signature K 4) (hM : (⟨a j.val,G j⟩ : AnySignature K)=⟨4,M⟩)
variable (e : Equiv.Perm (Fin 4))

def corolla : Labelling (BinaryInterpolation.Chains.reindex (Network.corolla M) e).shape s 1 a where
  vertex _ := j
  vertex_arity _ := congrArg Sigma.fst hM
  edge i := Fin.elim0 i

def literal (k : ℕ) : Labelling (C.literal M e k).shape s 1 a :=
  copies _ (corolla G j M hM e) k

theorem literal_exact (k : ℕ) : L.Exact G (C.literal M e k) (literal G j M hM e k) :=
  copies_exact G _ _ (fun _ => hM) k

private theorem apply_eq {n m : ℕ} (f : Signature K n) (g : Signature K m)
    (h : (⟨n,f⟩ : AnySignature K)=⟨m,g⟩) (hn : n=m) (x : Fin m→Bool) :
    f (fun i => x (Fin.cast hn i))=g x := by
  subst m
  have hf : f=g := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  simpa only [Fin.cast_eq_self] using congrFun hf x

def kernels (_ : Fin 1) : Kernel K := Signature.disequality

theorem template_actual (k : ℕ) :
    ((literal G j M hM e k).template.network (literal G j M hM e k).wellFormed G kernels).denote=
      (C.literal M e k).denote := by
  apply Labelling.denote_template_of_labels (literal G j M hM e k) G kernels
    (C.literal M e k).vertex (C.literal M e k).edge
  · intro v x
    exact apply_eq _ _ (literal_exact G j M hM e k v)
      ((literal G j M hM e k).vertex_arity v) x
  · intro i x y
    exact congrFun₂ (GeneralEOAffinePlaneChain.literal_native M e k i).symm x y

@[simp] theorem template_vertices (k : ℕ) :
    (literal G j M hM e k).template.vertices.length=k+1 := by
  rw [Labelling.vertices_length,GeneralEOAffinePlaneChain.literal_vertices]

@[simp] theorem template_edges (k : ℕ) :
    (literal G j M hM e k).template.edges.length=2*k := by
  rw [Labelling.edges_length,GeneralEOAffinePlaneChain.literal_edges]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOAffinePlaneChainLabels
