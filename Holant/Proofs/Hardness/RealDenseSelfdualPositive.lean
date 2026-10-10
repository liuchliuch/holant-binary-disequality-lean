import Holant.Proofs.Hardness.ThreeModeTriangleObstruction

/-! Any real selfdual triple with three nonzero coefficients yields a positive
triple by two literal original vertices and two native-X edges. The first
physical port order selects a same-sign pair; no sign oracle or free tensor is
introduced. This is a bounded access lemma, not a positive hardness endpoint. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSelfdualPositive
open Holant Holant.Complexity FixedGadgetSubstitution
namespace S
export ThreeModeSignatures (original)
end S
namespace R
export Holant.Complexity.BinaryInterpolation.Chains (reindex reindex_denote)
end R

/-- Indices denote identity, original port swap 2/3, and original swap 1/2. -/
def order (i : Fin 3) : Equiv.Perm (Fin 4) :=
  ![Equiv.refl _,SignedTwoCoefficientSignatures.middleSwap,TwoCoefficientSignatures.middleSwap] i

variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def triple (a b c : K) (i : Fin 3) : K×K×K := ![(a,b,c),(a,c,b),(c,b,a)] i

theorem reindex (a b c : K) (i : Fin 3) :
    Tensor.reindex (order i) (S.original a b c)=
      S.original (triple a b c i).1 (triple a b c i).2.1 (triple a b c i).2.2 := by
  fin_cases i
  · rfl
  · exact ThreeModeTriangleObstruction.swap_bc a b c
  · exact ThreeModeTriangleObstruction.swap_ac a b c

theorem same_sign (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    0<a*b ∨ 0<a*c ∨ 0<c*b := by
  rcases lt_or_gt_of_ne ha with ha|ha <;>
    rcases lt_or_gt_of_ne hb with hb|hb <;>
    rcases lt_or_gt_of_ne hc with hc|hc
  all_goals first
    | exact Or.inl (mul_pos ha hb)
    | exact Or.inl (mul_pos_of_neg_of_neg ha hb)
    | exact Or.inr (Or.inl (mul_pos ha hc))
    | exact Or.inr (Or.inl (mul_pos_of_neg_of_neg ha hc))
    | exact Or.inr (Or.inr (mul_pos hc hb))
    | exact Or.inr (Or.inr (mul_pos_of_neg_of_neg hc hb))

def choice (a b c : K) : Fin 3 := if 0<a*b then 0 else if 0<a*c then 1 else 2

theorem selected (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    0<(triple a b c (choice a b c)).1*(triple a b c (choice a b c)).2.1 ∧
      (triple a b c (choice a b c)).2.2≠0 := by
  unfold choice
  split_ifs with hab hac
  · exact ⟨hab,hc⟩
  · exact ⟨hac,hb⟩
  · exact ⟨((same_sign a b c ha hb hc).resolve_left hab).resolve_left hac,ha⟩

def one (a b c : K) (i : Fin 3) : Network K 4 :=
  R.reindex (Network.corolla (S.original a b c)) (order i)

def network (a b c : K) (i : Fin 3) : Network K 4 := ExactTwoChain.series (one a b c i) (one a b c i)

def positiveTriple (a b c : K) (i : Fin 3) : K×K×K :=
  let t := triple a b c i
  (2*t.1*t.2.1,t.1^2+t.2.1^2,t.2.2^2)

theorem denote (a b c : K) (i : Fin 3) :
    (network a b c i).denote=
      S.original (positiveTriple a b c i).1 (positiveTriple a b c i).2.1
        (positiveTriple a b c i).2.2 := by
  have ho : (one a b c i).denote=
      S.original (triple a b c i).1 (triple a b c i).2.1 (triple a b c i).2.2 := by
    rw [one,R.reindex_denote,Network.denote_corolla,reindex]
  rw [network,ThreeModeTriangleObstruction.series_original _ _ _ _ _ _ _ _ ho ho]
  unfold positiveTriple
  congr 1 <;> ring

theorem positive (a b c : K) (ha : a≠0) (hb : b≠0) (hc : c≠0) :
    0<(positiveTriple a b c (choice a b c)).1 ∧
    0<(positiveTriple a b c (choice a b c)).2.1 ∧
    0<(positiveTriple a b c (choice a b c)).2.2 := by
  have hs := selected a b c ha hb hc
  have hn : (triple a b c (choice a b c)).1≠0 := by
    intro hz
    simpa [hz] using hs.1
  change 0<2*(triple a b c (choice a b c)).1*(triple a b c (choice a b c)).2.1 ∧ _
  exact ⟨by nlinarith [hs.1],
    add_pos_of_pos_of_nonneg (sq_pos_of_ne_zero hn) (sq_nonneg _),sq_pos_of_ne_zero hs.2⟩

def labels (a b c : K) (i : Fin 3) : Labelling (network a b c i).shape 1 1 (fun _=>4) where
  vertex _ := 0
  vertex_arity v := by fin_cases v <;> rfl
  edge _ := 0
abbrev template (a b c : K) (i : Fin 3) := (labels a b c i).template

theorem valid (a b c : K) (i : Fin 3) :
    (template a b c i).WellFormed 1 1 (fun _=>4) := (labels a b c i).wellFormed

theorem counts (a b c : K) (i : Fin 3) :
    (template a b c i).vertices.length=2 ∧ (template a b c i).edges.length=2 := by
  fin_cases i <;> exact ⟨rfl,rfl⟩

def rows (i : Fin 3) : List (ℕ × List (ℕ ⊕ (ℕ × Bool))) := ![
  [(0,[.inl 0,.inr (1,false),.inl 2,.inr (0,false)]),
   (0,[.inr (1,true),.inl 1,.inr (0,true),.inl 3])],
  [(0,[.inl 0,.inr (1,false),.inr (0,false),.inl 2]),
   (0,[.inr (1,true),.inl 1,.inl 3,.inr (0,true)])],
  [(0,[.inl 0,.inl 2,.inr (1,false),.inr (0,false)]),
   (0,[.inr (1,true),.inr (0,true),.inl 1,.inl 3])]] i

theorem records (a b c : K) (i : Fin 3) :
    (template a b c i).boundary=4 ∧ (template a b c i).vertices=rows i ∧
      (template a b c i).edges=[0,0] := by
  fin_cases i <;> exact ⟨rfl,rfl,rfl⟩

theorem template_denote (a b c : K) (i : Fin 3) :
    ((template a b c i).network (valid a b c i) (fun _ : Fin 1=>S.original a b c)
      (fun _ : Fin 1=>Signature.disequality)).denote=
      S.original (positiveTriple a b c i).1 (positiveTriple a b c i).2.1
        (positiveTriple a b c i).2.2 := by
  rw [←denote]
  apply Labelling.denote_template_of_labels (labels a b c i) _ _ (network a b c i).vertex (network a b c i).edge
  · intro v x; fin_cases v <;> rfl
  · intro e x y; fin_cases e <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseSelfdualPositive
