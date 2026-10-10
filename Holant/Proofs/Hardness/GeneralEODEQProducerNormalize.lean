import Holant.Proofs.Hardness.GeneralEODEQProducerReduction
import Holant.Proofs.Hardness.GeneralEOAffineNetworkChain

/-! Two actual copies of the reduced weighted antipodal row realize the
central DEQ4 row. Crossing the native edges makes the compressed matrix
square equal to a nonzero scalar identity; no root-of-unity or interpolation
hypothesis is used, and no equality vertex is adjoined. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerNormalize
open Holant Holant.Complexity FixedGadgetSubstitution
open GeneralEODEQProducerCore
open scoped Matrix
namespace C
export GeneralEOAffinePlaneChain (Mat binary table bitIndex)
end C
namespace A
export GeneralEOAffineNetworkChain (network labels exact native power_denote)
end A
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] {s : ℕ} {a : ℕ → ℕ}

def first : Fin 4 → Bool := ![false,true,true,false]
def second : Fin 4 → Bool := ![true,false,false,true]

def weighted (c d : K) : Signature K 4 :=
  EOBinaryPlaneCore.lift (C.binary !![0,c;d,0])

theorem weighted_value (c d : K) (x : Fin 4 → Bool) :
    weighted c d x=if x=first then c else if x=second then d else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [weighted,EOBinaryPlaneCore.lift,C.binary,C.bitIndex,first,second,
      funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

theorem middle_word (x : Fin 4 → Bool) (hx : 2*weight x=4) :
    ∃i : Fin 6,x=FiveSupportEOOrdering.middleWord i := by
  revert x
  decide

def order (i : Fin 6) : Equiv.Perm (Fin 4) :=
  (FiveSupportEOOrdering.orderAt i).trans (FiveSupportEOOrdering.orderAt 2).symm

theorem first_order (i : Fin 6) :
    (fun j => first (order i j))=FiveSupportEOOrdering.middleWord i := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

theorem second_order (i : Fin 6) :
    (fun j => second (order i j))=fun j => !(FiveSupportEOOrdering.middleWord i j) := by
  funext j
  fin_cases i <;> fin_cases j <;> rfl

/-- A boundary permutation puts the literal isolated row at the off-diagonal
binary plane, preserving its two actual nonzero coefficients. -/
theorem oriented (f : Signature K 4) (he : Signature.CentralSupport f) (p : Pair f) :
    ∃e : Equiv.Perm (Fin 4),∃c d : K,c≠0 ∧ d≠0 ∧ Tensor.reindex e f=weighted c d := by
  have hm : D.distance p.left p.right=4 := by
    have hl := distance_le p.left p.right
    have hd := p.distant
    omega
  have hb := complementary_of_max p.left p.right hm
  obtain ⟨i,hi⟩ := middle_word p.left (central_word f he p.left p.left_supported)
  have hf : (fun j => first (order i j))=p.left := (first_order i).trans hi.symm
  have hs : (fun j => second (order i j))=p.right := by rw [second_order,←hi,←hb]
  refine ⟨order i,f p.left,f p.right,p.left_supported,p.right_supported,?_⟩
  funext x
  rw [Tensor.reindex_apply,weighted_value]
  by_cases hx : x=first
  · subst x
    simp only [ite_true,hf]
  · by_cases hy : x=second
    · subst x
      simp only [hx,ite_false,ite_true,hs]
    · simp only [hx,hy,ite_false]
      by_contra hn
      have hept := p.isolated (fun j => x (order i j)) hn (fun j hj =>
        False.elim ((distance_eq_iff p.left p.right).mp hm j hj))
      rcases hept with h | h
      · apply hx
        funext j
        have hh := congrFun (h.trans hf.symm) ((order i).symm j)
        simpa using hh
      · apply hy
        funext j
        have hh := congrFun (h.trans hs.symm) ((order i).symm j)
        simpa using hh

theorem square (c d : K) :
    C.table (C.binary !![0,c;d,0])^2=(c*d) • (1 : C.Mat (K:=K)) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [C.table,C.binary,C.bitIndex,pow_two,Matrix.mul_apply,Fin.sum_univ_two,mul_comm]

structure Produced (G : (i : Fin s) → Signature K (a i.val)) where
  network : Network K 4
  labels : Labelling network.shape s 1 a
  exact : LabelledNetwork.Exact G network labels
  native : ∀e,network.edge e=Signature.disequality
  scalar : K
  nonzero : scalar≠0
  denote : network.denote=scalar • ExactTwoSignatures.E

/-- The supplier is the literal two-copy chain over the inherited labels. -/
theorem produce_reduced (G : (i : Fin s) → Signature K (a i.val))
    (R : GeneralEODEQProducerReduction.Reduced G) : Nonempty (Produced G) := by
  obtain ⟨e,c,d,hc,hd,hp⟩ := oriented R.network.denote R.central R.pair
  exact ⟨⟨A.network R.network e 1,A.labels R.network R.labels e 1,
    A.exact R.network R.labels e G R.exact 1,A.native R.network e R.native 1,
    c*d,mul_ne_zero hc hd,
    A.power_denote R.network e (C.binary !![0,c;d,0]) hp 1 (c*d) (square c d)⟩⟩

/-- From any actual labelled central network with an isolated supported
interval of distance at least four, paired pins produce central DEQ4. -/
theorem produce (G : (i : Fin s) → Signature K (a i.val)) (j : Fin s)
    (hj : (⟨a j.val,G j⟩ : AnySignature K)=⟨2,GeneralEOPinnedDescentNetwork.directed01⟩)
    {n : ℕ} (T : Network K n) (TL : Labelling T.shape s 1 a)
    (hE : LabelledNetwork.Exact G T TL) (hN : ∀e,T.edge e=Signature.disequality)
    (hC : Signature.CentralSupport T.denote) (p : Pair T.denote) : Nonempty (Produced G) := by
  obtain ⟨R⟩ := GeneralEODEQProducerReduction.reduce G j hj n T TL hE hN hC p
  exact produce_reduced G R

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEODEQProducerNormalize
