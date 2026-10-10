import Holant.Certificates.EqualityQuaternary.C2FirstFlip
import Holant.Certificates.EqualityQuaternary.C2MixedExit

/-! The mixed-sign normal form is derived from the original physical deck.
The finite sign selection is checked over all three original complementary
blocks; actual normalization is at most one I attachment and a port order.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.C2.Mixed
open Holant Holant.Marked Holant.Tractable
open Holant.Projective.CyclicQuaternary
open Holant.Projective.CyclicQuaternary.Physical hiding Scalar Mat Representatives
open Holant.Marked.SupportAtlas (reorder permuteWord coordinateAction_reorder)
open Holant.Certificates.FourthRootOdd
set_option backward.isDefEq.respectTransparency false

def blockData (a : Signature Scalar 4) (i : Fin 3) : Option Bool :=
  if (coordinates a i).1=0 then none else
    if (coordinates a i).2=(coordinates a i).1 then some false else some true

theorem data_none (a : Signature Scalar 4) (i : Fin 3)
    (hs : SafeBlock (endpoint0 a) (endpoint1 a) (coordinates a i).1 (coordinates a i).2)
    (h : blockData a i=none) : (coordinates a i).1=0 ∧ (coordinates a i).2=0 := by
  have hx : (coordinates a i).1=0 := by
    by_contra hx
    simp [blockData,hx] at h
    split_ifs at h <;> contradiction
  exact ⟨hx,(active_zero_iff hs).mp hx⟩

theorem data_some (a : Signature Scalar 4) (i : Fin 3)
    (hs : SafeBlock (endpoint0 a) (endpoint1 a) (coordinates a i).1 (coordinates a i).2)
    (b : Bool) (h : blockData a i=some b) :
    (coordinates a i).1≠0 ∧ (coordinates a i).2=sign b*(coordinates a i).1 := by
  have hx : (coordinates a i).1≠0 := by intro hx; simp [blockData,hx] at h
  refine ⟨hx,?_⟩
  have he := ((safeBlock_iff _ _ _ _).mp hs).2.1
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp he with hy | hy
  · have hb : b=false := by simpa [blockData,hx,hy] using h.symm
    simp [hb,sign,hy]
  · by_cases hh : (coordinates a i).2=(coordinates a i).1
    · have hb : b=false := by simpa [blockData,hx,hh] using h.symm
      simp [hb,sign,hh]
    · have hb : b=true := by simpa [blockData,hx,hh] using h.symm
      simp [hb,sign,hy]

theorem select_signs : ∀ d : Fin 3 → Option Bool,
    (¬∃ b : Bool,∀ i,d i=none ∨ d i=some b) →
    ∃ (b : Bool) (e : Equiv.Perm (Fin 3)),
      d (e 0)=some b ∧ (d (e 1)=none ∨ d (e 1)=some b) ∧ d (e 2)=some (!b) := by
  decide +kernel

def rowPermutation (e : Equiv.Perm (Fin 3)) : Equiv.Perm (Fin 4) where
  toFun := Fin.cases 0 (fun j => (e j).succ)
  invFun := Fin.cases 0 (fun j => (e.symm j).succ)
  left_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp
  right_inv i := by refine Fin.cases rfl (fun j => ?_) i; simp

theorem pair_word : ∀ (e : Equiv.Perm (Fin 3)) (i : Fin 3) (a : Bool),
    permuteWord (rowPermutation e) (join i false a a (!a) (!a))=
      join (e i) false a a (!a) (!a) := by decide +kernel

theorem odd_word : ∀ (e : Equiv.Perm (Fin 3)) (w : Word),
    odd (permuteWord (rowPermutation e) w)=odd w := by decide +kernel

theorem coordinates_reorder (a : Signature Scalar 4) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    coordinates (reorder a (rowPermutation e)) i=coordinates a (e i) := by
  apply Prod.ext
  · change a (permuteWord (rowPermutation e) (join i false true true false false))=_
    exact congrArg a (pair_word e i true)
  · change a (permuteWord (rowPermutation e) (join i false false false true true))=_
    exact congrArg a (pair_word e i false)

def normalized (q : Signature Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) : Signature Scalar 4 :=
  reorder (if b then firstFlip q else q) (rowPermutation e)
def normalizedNetwork (N : Network Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) : Network Scalar 4 :=
  reorderNetwork (if b then firstFlipNetwork N else N) (rowPermutation e).symm

theorem normalized_denote (N : Network Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) :
    (normalizedNetwork N b e).denote=normalized N.denote b e := by
  rw [normalizedNetwork,reorderNetwork_denote]
  cases b <;> simp [normalized,firstFlip_denote]
  all_goals rfl

theorem normalized_allowed {q : Signature Scalar 4} {N : Network Scalar 4}
    (h : Counted.Allowed q N) (b : Bool) (e : Equiv.Perm (Fin 3)) :
    Counted.Allowed q (normalizedNetwork N b e) := by
  cases b
  · exact h.reorder _
  · exact (firstFlip_allowed h).reorder _

theorem normalized_copies (N : Network Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) :
    Counted.copies (normalizedNetwork N b e)=Counted.copies N := by
  cases b <;> simp [normalizedNetwork,firstFlip_copies]

theorem normalized_prime {q : Signature Scalar 4} (hp : TensorPrime q)
    (b : Bool) (e : Equiv.Perm (Fin 3)) : TensorPrime (normalized q b e) := by
  cases b
  · exact prime_reindex hp (rowPermutation e).symm
  · exact prime_reindex (flip_prime hp firstMask) (rowPermutation e).symm

theorem normalized_walsh (q : Signature Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) :
    walsh (normalized q b e)=reorder (walsh (if b then firstFlip q else q)) (rowPermutation e) :=
  coordinateAction_reorder Pinv _ _

theorem normalized_coordinates (q : Signature Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3)) (i : Fin 3) :
    coordinates (walsh (normalized q b e)) i=
      (sign b*(coordinates (walsh q) (e i)).1,(coordinates (walsh q) (e i)).2) := by
  rw [normalized_walsh,coordinates_reorder]
  cases b
  · simp [sign]
  · generalize e i=j
    fin_cases j <;> apply Prod.ext <;>
      simp [coordinates,firstFlip_walsh,join,sign]

theorem normalized_even (q : Signature Scalar 4) (he : EvenSupported (walsh q))
    (b : Bool) (e : Equiv.Perm (Fin 3)) : EvenSupported (walsh (normalized q b e)) := by
  intro w hw
  rw [normalized_walsh]
  change walsh (if b then firstFlip q else q) (permuteWord (rowPermutation e) w)=0
  have ho : odd (permuteWord (rowPermutation e) w)=true := by rw [odd_word,hw]
  cases b
  · exact he _ ho
  · simp only [ite_true]
    rw [firstFlip_walsh,he _ ho,mul_zero]

theorem normalized_endpoints (q : Signature Scalar 4) (b : Bool) (e : Equiv.Perm (Fin 3))
    (h0 : endpoint0 (walsh q)=0) (h1 : endpoint1 (walsh q)=0) :
    endpoint0 (walsh (normalized q b e))=0 ∧ endpoint1 (walsh (normalized q b e))=0 := by
  have hf (v : Bool) : permuteWord (rowPermutation e) (fun _ => v)=(fun _ => v) := rfl
  rw [normalized_walsh]
  have he0 : (![false,false,false,false] : Word)=(fun _ => false) := by decide
  have he1 : (![true,true,true,true] : Word)=(fun _ => true) := by decide
  simp only [endpoint0,endpoint1,he0,he1] at h0 h1 ⊢
  cases b <;> simp [reorder,hf,firstFlip_walsh,h0,h1]

theorem source_mixed_normalization {F : SignatureFamily Scalar} (reps : C2.Representatives F)
    (q : Signature Scalar 4) (hd : C2.PhysicalDeck reps q) (hmixed : ¬OneCopyCase q) :
    ∃ (b : Bool) (e : Equiv.Perm (Fin 3)) (x y z : Scalar), x≠0 ∧ z≠0 ∧
      walsh (normalized q b e)=mixedTable x y z := by
  have hs := safe_blocks (walsh q) (physical_walshSafe reps q hd)
  have he := odd_coefficients_zero (walsh q) (physical_walshSafe reps q hd)
  have h0 : endpoint0 (walsh q)=0 := by
    by_contra h0
    exact hmixed (Or.inl h0)
  have h1 := (endpoints_zero_iff (hs 0)).mp h0
  have hnot : ¬∃ b : Bool,∀ i,blockData (walsh q) i=none ∨ blockData (walsh q) i=some b := by
    rintro ⟨b,hb⟩
    apply hmixed
    right
    refine ⟨sign b,by cases b <;> simp [sign],?_⟩
    intro i hi
    rcases hb i with hz | hz
    · exact (hi (data_none _ i (hs i) hz).1).elim
    · rw [(data_some _ i (hs i) b hz).2]
      exact mul_div_cancel_right₀ _ hi
  obtain ⟨b,e,hleft,hmid,hright⟩ := select_signs (blockData (walsh q)) hnot
  let a := walsh (normalized q b e)
  have hn (i : Fin 3) (v : Bool) (hv : blockData (walsh q) (e i)=some v) :
      (coordinates a i).1≠0 ∧ (coordinates a i).2=sign (v ^^ b)*(coordinates a i).1 := by
    obtain ⟨hx,hy⟩ := data_some _ _ (hs (e i)) v hv
    rw [show a=walsh (normalized q b e) from rfl,normalized_coordinates]
    constructor
    · cases b <;> simpa [sign] using hx
    · simp only [hy]
      cases v <;> cases b <;> simp [sign]
  have hl := hn 0 b hleft
  have hr := hn 2 (!b) hright
  have hm : (coordinates a 1).2=(coordinates a 1).1 := by
    rcases hmid with hz | hz
    · obtain ⟨hx,hy⟩ := data_none _ _ (hs (e 1)) hz
      change (coordinates (walsh (normalized q b e)) 1).2=_
      rw [normalized_coordinates]
      simp [hx,hy]
    · simpa [sign] using (hn 1 b hz).2
  have hl' : (coordinates a 0).2=(coordinates a 0).1 := by simpa [sign] using hl.2
  have hr' : (coordinates a 2).2=-(coordinates a 2).1 := by
    cases b <;> simpa [sign] using hr.2
  refine ⟨b,e,(coordinates a 0).1,(coordinates a 1).1,(coordinates a 2).1,hl.1,hr.1,?_⟩
  have hc : coordinates a = ![((coordinates a 0).1,(coordinates a 0).1),
      ((coordinates a 1).1,(coordinates a 1).1),((coordinates a 2).1,-(coordinates a 2).1)] := by
    funext i
    fin_cases i
    · exact Prod.ext rfl hl'
    · exact Prod.ext rfl hm
    · exact Prod.ext rfl hr'
  have hv := normalized_endpoints q b e h0 h1
  have ha := ofCoordinates_extract a (normalized_even q he b e)
  rw [hv.1,hv.2,hc] at ha
  exact ha.symm

end Holant.Certificates.EqualityQuaternary.C2.Mixed
