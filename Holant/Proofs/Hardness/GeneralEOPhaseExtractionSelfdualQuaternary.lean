import Holant.Proofs.Hardness.GeneralEOPhaseExtractionQuaternary
import Holant.Proofs.Hardness.ExactTwoSignatures

/-! Exact selfdual quaternary residual. Missing complementary support gives
an actual coordinate plane. Its zero, tied two-support, full product, and full
nonproduct cases are kept separate. No compression is made a free vertex. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualQuaternary
open Holant Holant.Tractable
namespace F
export SelfDualPinObstruction (flip SelfDual)
end F
namespace B
export EOBinaryPlaneCore (word lift compress normalized normalized_lift)
end B
namespace O
export FiveSupportEOOrdering (middleWord middleCoeff orderAt)
end O
namespace Q
export GeneralEOPhaseExtractionQuaternary (flip_two flip_middle dense_of_middle)
end Q
namespace C
export EOBinaryPlaneClassification (Full full_product_iff Cross)
end C
set_option backward.isDefEq.respectTransparency false

def tied (c : AlgebraicComplex) (opposite : Bool) : Signature AlgebraicComplex 2 :=
  fun x => if Bool.xor (x 0) (x 1)=opposite then c else 0

def product (c : AlgebraicComplex) (minus : Bool) : Signature AlgebraicComplex 2 :=
  fun x => if minus && Bool.xor (x 0) (x 1) then -c else c

/-- A tied block has only two supported words. A full product block has all
four words and either the same coefficient or the signed tensor-square pattern. -/
def Residual (f : Signature AlgebraicComplex 2) : Prop :=
  f=0 ∨ (∃c,c≠0 ∧ ∃b,f=tied c b) ∨
    (∃c,c≠0 ∧ ∃b,f=product c b) ∨ (C.Full f ∧ ¬Product f)

theorem selfdual_values (f : Signature AlgebraicComplex 2) (hS : F.SelfDual f) :
    f ![true,true]=f ![false,false] ∧ f ![true,false]=f ![false,true] := by
  exact ⟨by simpa only [Q.flip_two,Bool.not_false] using hS ![false,false],
    by simpa only [Q.flip_two,Bool.not_false,Bool.not_true] using hS ![false,true]⟩

theorem binary_residual (f : Signature AlgebraicComplex 2) (hS : F.SelfDual f) : Residual f := by
  classical
  obtain ⟨h11,h10⟩ := selfdual_values f hS
  have words (x : Fin 2 → Bool) : x=![x 0,x 1] := by
    funext i
    fin_cases i <;> rfl
  by_cases h0 : f ![false,false]=0
  · by_cases h1 : f ![false,true]=0
    · left
      funext x
      rw [words x]
      cases x 0 <;> cases x 1 <;> simp [h11,h10,h0,h1]
    · right; left
      refine ⟨f ![false,true],h1,true,?_⟩
      funext x
      rw [words x]
      cases x 0 <;> cases x 1 <;> simp [tied,h11,h10,h0]
  by_cases h1 : f ![false,true]=0
  · right; left
    refine ⟨f ![false,false],h0,false,?_⟩
    funext x
    rw [words x]
    cases x 0 <;> cases x 1 <;> simp [tied,h11,h10,h1]
  have hfull : C.Full f := by
    intro x
    rw [words x]
    cases x 0 <;> cases x 1 <;> simp [h11,h10,h0,h1]
  by_cases hp : Product f
  · have hc := (C.full_product_iff f hfull).mp hp
    have hs : f ![false,false]^2=f ![false,true]^2 := by
      change f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false] at hc
      rw [h11,h10] at hc
      simpa only [pow_two] using hc
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he|he
    · right; right; left
      refine ⟨f ![false,false],h0,false,?_⟩
      funext x
      rw [words x]
      cases x 0 <;> cases x 1 <;> simp [product,h11,h10,he]
    · right; right; left
      refine ⟨f ![false,false],h0,true,?_⟩
      have he' : f ![false,true]= -f ![false,false] := by linear_combination he
      funext x
      rw [words x]
      cases x 0 <;> cases x 1 <;> simp [product,h11,h10,he']
  · exact Or.inr (Or.inr (Or.inr ⟨hfull,hp⟩))

theorem compressed_selfdual (M : Signature AlgebraicComplex 4)
    (hS : F.SelfDual M) (e : Equiv.Perm (Fin 4)) :
    F.SelfDual (B.compress (Tensor.reindex e M)) := by
  intro x
  have hf : B.word (F.flip x)=F.flip (B.word x) := by
    funext i
    fin_cases i <;> rfl
  change M (B.word (F.flip x) ∘ e)=M (B.word x ∘ e)
  rw [hf]
  exact hS (B.word x ∘ e)

/-- This is the full support classification needed before the k=1 matching
argument. In particular, a two-supported DEQ-type block is an explicit outcome. -/
theorem dense_or_plane_residual (M : Signature AlgebraicComplex 4)
    (hE : Signature.CentralSupport M) (hS : F.SelfDual M) :
    (∀x,weight x=2 → M x≠0) ∨
    ∃e : Equiv.Perm (Fin 4),
      Tensor.reindex e M=B.lift (B.compress (Tensor.reindex e M)) ∧
      Residual (B.compress (Tensor.reindex e M)) := by
  classical
  by_cases hd : ∀i : Fin 6,O.middleCoeff M i≠0
  · exact Or.inl (Q.dense_of_middle M hd)
  · push Not at hd
    obtain ⟨i,hi⟩ := hd
    have ho : O.middleCoeff M (5-i)=0 := by
      have h := hS (O.middleWord i)
      rw [Q.flip_middle] at h
      exact h.trans hi
    have he : DenseEOUnitLocal.EOSupport M := by
      intro x hx
      apply hE
      omega
    refine Or.inr ⟨O.orderAt i,?_,binary_residual _ (compressed_selfdual M hS _)⟩
    exact (B.normalized_lift M he i hi ho).symm

/-- Product compression with selfduality cannot carry an arbitrary phase
ratio: its opposite entries are exactly equal or negatives. -/
theorem full_product_exact (f : Signature AlgebraicComplex 2) (hS : F.SelfDual f)
    (hfull : C.Full f) (hP : Product f) : ∃c,c≠0 ∧ ∃b,f=product c b := by
  rcases binary_residual f hS with hz|ht|hp|hnp
  · exact False.elim (hfull ![false,false] (congrFun hz _))
  · obtain ⟨c,hc,b,h⟩ := ht
    cases b
    · exact False.elim (hfull ![false,true] (by simp [h,tied]))
    · exact False.elim (hfull ![false,false] (by simp [h,tied]))
  · exact hp
  · exact False.elim (hnp.2 hP)

def tiedOrder (b : Bool) : Equiv.Perm (Fin 4) :=
  if b then Equiv.swap 2 3 else Equiv.refl _

/-- Each nonzero tied block is already scaled DEQ4 after one actual boundary
permutation. No tensor product or compression is installed as a vertex. -/
theorem tied_deq (c : AlgebraicComplex) (b : Bool) :
    Tensor.reindex (tiedOrder b) (B.lift (tied c b))=c • ExactTwoSignatures.E := by
  funext x
  have hx : x=![x 0,x 1,x 2,x 3] := by
    funext i
    fin_cases i <;> rfl
  rw [hx]
  cases b <;> cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;>
    simp [tiedOrder,Tensor.reindex,B.lift,tied,ExactTwoSignatures.E_reference,
      Pi.smul_apply,smul_eq_mul,Equiv.swap_apply_def]

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPhaseExtractionSelfdualQuaternary
