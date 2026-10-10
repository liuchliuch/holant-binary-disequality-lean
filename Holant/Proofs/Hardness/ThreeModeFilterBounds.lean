import Holant.Proofs.Hardness.ThreeModeFilter
import Holant.Complexity.BinaryInterpolation.RingFormulaMachine

/-! Linear-growth arithmetic height certificates for the actual adjacent-vector
filter. Addition increases the expansion budget by one; a factor adds its own
budget. No exponential formula tree is constructed or assumed small. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeFilter
open Holant.OneHot Holant.Complexity Holant.Algebraic
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

section Algebra
variable {K A : Type} [Field K] [Algebra ℚ K]
variable (base : A→K) (unit minus : A) (hunit : base unit=1) (hminus : base minus = -1)

def Bounded (R U : ℕ) (s : State K) : Prop :=
  (∀ r∈s.1.1,ArithmeticSize.Bound base R r) ∧
  (∀ y∈s.1.2,ArithmeticSize.Bound base U y) ∧
  ArithmeticSize.Bound base R s.2.1 ∧ ArithmeticSize.Bound base U s.2.2

include unit hunit in
theorem getD_bound (xs : List K) (B k : ℕ)
    (h : ∀ x∈xs,ArithmeticSize.Bound base B x) :
    ArithmeticSize.Bound base B (xs.getD k 0) := by
  by_cases hk : k<xs.length
  · rw [List.getD_eq_getElem _ _ hk]
    exact h _ (List.getElem_mem hk)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact ArithmeticSize.Bound.zero unit B

include unit minus hunit hminus in
theorem sub_bound {x y : K} {B : ℕ}
    (hx : ArithmeticSize.Bound base B x) (hy : ArithmeticSize.Bound base B y) :
    ArithmeticSize.Bound base (B+2) (x-y) := by
  have hn : ArithmeticSize.Bound base 1 (-1 : K) := by
    simpa only [hminus] using (ArithmeticSize.Bound.coefficient (coeff:=base) minus)
  have hb := (hx.mono unit hunit (show B≤B+1 by omega)).add unit hunit
    ((hn.mul hy).mono unit hunit (by omega : 1+B≤B+1))
  simpa only [neg_one_mul,sub_eq_add_neg] using hb

include unit minus hunit hminus in
theorem difference_bound {r : K} {ys : List K} {R U : ℕ}
    (hr : ArithmeticSize.Bound base R r)
    (hy : ∀ y∈ys,ArithmeticSize.Bound base U y) :
    ∀ y∈difference r ys,ArithmeticSize.Bound base (U+R+2) y := by
  intro y hy'
  obtain ⟨k,hk,rfl⟩ := List.mem_map.mp hy'
  have ha := getD_bound base unit hunit ys U k hy
  have hb := getD_bound base unit hunit ys U (k+1) hy
  have hp := hr.mul ha
  apply sub_bound base unit minus hunit hminus
  · exact hb.mono unit hunit (by omega)
  · exact hp.mono unit hunit (by omega)

include unit minus hunit hminus in
theorem bounded_step {R U : ℕ} {s : State K} (h : Bounded base R U s) :
    Bounded base R (U+R+2) (step s) := by
  obtain ⟨hr,hy,hw,hd⟩ := h
  by_cases he : s.1.1=[]
  · simp only [step,he,if_true]
    exact ⟨hr,fun y hy' => (hy y hy').mono unit hunit (by omega),hw,
      hd.mono unit hunit (by omega)⟩
  · simp only [step,he,if_false]
    have hhead := getD_bound base unit hunit s.1.1 R 0 hr
    refine ⟨?_,difference_bound base unit minus hunit hminus hhead hy,hw,?_⟩
    · intro r hm
      exact hr r (List.mem_of_mem_tail hm)
    · have hfactor := sub_bound base unit minus hunit hminus hw hhead
      simpa only [Nat.add_assoc] using hd.mul hfactor

include unit minus hunit hminus in
theorem bounded_iterate {R U : ℕ} {s : State K} (h : Bounded base R U s) (k : ℕ) :
    Bounded base R (U+k*(R+2)) ((step^[k]) s) := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have ht := bounded_step base unit minus hunit hminus ih
    have he : U+(k+1)*(R+2)=U+k*(R+2)+R+2 := by ring
    rw [he]
    exact ht

theorem length_step (s : State K) :
    (step s).1.1.length≤s.1.1.length ∧ (step s).1.2.length≤s.1.2.length := by
  unfold step
  split_ifs <;> simp only [List.length_tail,difference_length,le_refl,and_self]
  exact ⟨Nat.sub_le _ _,Nat.sub_le _ _⟩

theorem length_iterate (s : State K) (k : ℕ) :
    ((step^[k]) s).1.1.length≤s.1.1.length ∧
      ((step^[k]) s).1.2.length≤s.1.2.length := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    have ht := length_step ((step^[k]) s)
    exact ⟨ht.1.trans ih.1,ht.2.trans ih.2⟩
end Algebra

section Encoding
variable {K A : Type} [Field K] [Algebra ℚ K] [Fintype A] {n : ℕ}
variable (F : FixedField K n) (base : A→Fin n→ℚ)
variable (unit minus : A) (hunit : F.decode (base unit)=1) (hminus : F.decode (base minus) = -1)

theorem list_length_bound (ys : List K) (W : ℕ)
    (hy : ∀ y∈ys,(F.encoding.encode y).length≤W) :
    ((listEncoding F).encode ys).length≤(2*W+2)*ys.length+1 := by
  induction ys with
  | nil => simp [listEncoding,framedListEncoding,framedListEncode]
  | cons y ys ih =>
    have ha := hy y (by simp)
    have ht := ih (fun z hz => hy z (by simp [hz]))
    change (true::(frame (F.encoding.encode y)++framedListEncode F.encoding ys)).length≤_
    simp only [List.length_cons,List.length_append,frame_length]
    change (framedListEncode F.encoding ys).length≤_ at ht
    nlinarith

theorem encoding_length (s : State K) : (encoding F |>.encode s).length=
    4*((listEncoding F).encode s.1.1).length+2*((listEncoding F).encode s.1.2).length+
      2*(F.encoding.encode s.2.1).length+(F.encoding.encode s.2.2).length+4 := by
  simp only [encoding,vectorsEncoding,scalarsEncoding,FixedFieldMachines.pairEncoding_length]
  omega

include unit hunit in
theorem bounded_encoding {R U B L : ℕ} {s : State K}
    (h : Bounded (fun a=>F.decode (base a)) R U s) (hr : R≤B) (hu : U≤B)
    (hl : s.1.1.length≤L ∧ s.1.2.length≤L) :
    (encoding F |>.encode s).length≤
      6*(2*ArithmeticSize.bitBound F base B+2)*L+3*ArithmeticSize.bitBound F base B+10 := by
  have root_width : ∀r∈s.1.1,(F.encoding.encode r).length≤ArithmeticSize.bitBound F base B :=
    fun r hm => ((h.1 r hm).mono unit hunit hr).encoded_length_le F base
  have answer_width : ∀y∈s.1.2,(F.encoding.encode y).length≤ArithmeticSize.bitBound F base B :=
    fun y hm => ((h.2.1 y hm).mono unit hunit hu).encoded_length_le F base
  have hw := (h.2.2.1.mono unit hunit hr).encoded_length_le F base
  have hd := (h.2.2.2.mono unit hunit hu).encoded_length_le F base
  have hrs := list_length_bound F s.1.1 _ root_width
  have hys := list_length_bound F s.1.2 _ answer_width
  have hm₁ := Nat.mul_le_mul_left (2*ArithmeticSize.bitBound F base B+2) hl.1
  have hm₂ := Nat.mul_le_mul_left (2*ArithmeticSize.bitBound F base B+2) hl.2
  rw [encoding_length]
  nlinarith

theorem list_counts_le_bytes (s : State K) :
    s.1.1.length≤(encoding F |>.encode s).length ∧
      s.1.2.length≤(encoding F |>.encode s).length := by
  have hr := framedListEncoding_length_lower F.encoding s.1.1
  have hy := framedListEncoding_length_lower F.encoding s.1.2
  rw [encoding_length]
  change _≤((listEncoding F).encode s.1.1).length at hr
  change _≤((listEncoding F).encode s.1.2).length at hy
  omega

include unit minus hunit hminus in
theorem iterate_encoding {R U L : ℕ} {s : State K}
    (h : Bounded (fun a=>F.decode (base a)) R U s)
    (hs : (encoding F |>.encode s).length≤L) (i : ℕ) (hi : i≤L) :
    (encoding F |>.encode ((step^[i]) s)).length≤
      6*(2*ArithmeticSize.bitBound F base (R+U+L*(R+2))+2)*L+
        3*ArithmeticSize.bitBound F base (R+U+L*(R+2))+10 := by
  have hb := bounded_iterate (fun a=>F.decode (base a)) unit minus hunit hminus h i
  have hl := length_iterate s i
  have hcounts := list_counts_le_bytes F s
  apply bounded_encoding F base unit hunit hb
  · omega
  · have hm := Nat.mul_le_mul_right (R+2) hi
    omega
  · exact ⟨hl.1.trans (hcounts.1.trans hs),hl.2.trans (hcounts.2.trans hs)⟩

end Encoding
end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ThreeModeFilter
