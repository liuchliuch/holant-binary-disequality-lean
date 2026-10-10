import Holant.Proofs.Hardness.GeneralEOPairedFamilyExtractionSupportGeometry

/-! Exact support reconstruction in the remaining intersection-closed branch.
Every active coordinate class has a supported indicator word, derived by finite
intersection. The entire support is precisely the inactive-coordinate pins
and equality classes; no support decomposition is supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionComponents
open Holant Holant.Tractable GeneralEOPairedFamilyExtractionSupport
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (f : Signature AlgebraicComplex n)

def Active (i : Fin n) : Prop := ∃w,f w≠0 ∧ w i=true
def Same (i j : Fin n) : Prop := ∀w,f w≠0 → w i=w j

theorem same_refl (i : Fin n) : Same f i i := fun _ _ => rfl
theorem same_symm {i j : Fin n} (h : Same f i j) : Same f j i := fun w hw => (h w hw).symm
theorem same_trans {i j k : Fin n} (h : Same f i j) (h' : Same f j k) : Same f i k :=
  fun w hw => (h w hw).trans (h' w hw)

def base (i : Fin n) (hi : Active f i) : Fin n → Bool := Classical.choose hi

theorem base_supported (i : Fin n) (hi : Active f i) : f (base f i hi)≠0 := (Classical.choose_spec hi).1
theorem base_true (i : Fin n) (hi : Active f i) : base f i hi i=true := (Classical.choose_spec hi).2

variable (hx : XorClosed f)

include hx in
theorem separator_exists (i : Fin n) (hi : Active f i) (j : Fin n) :
    ∃w,f w≠0 ∧ w i=true ∧ (¬Same f i j → w j=false) := by
  by_cases hs : Same f i j
  · exact ⟨base f i hi,base_supported f i hi,base_true f i hi,fun hn => False.elim (hn hs)⟩
  · have hn : ∃w,f w≠0 ∧ w i≠w j := by simpa only [Same,not_forall,not_imp,exists_prop] using hs
    obtain ⟨w,hw,hwne⟩ := hn
    by_cases hwi : w i=true
    · have hwj : w j=false := by cases hj : w j <;> simp_all
      exact ⟨w,hw,hwi,fun _ => hwj⟩
    · have hwif : w i=false := by cases h : w i <;> simp_all
      have hwjt : w j=true := by cases h : w j <;> simp_all
      by_cases hbj : base f i hi j=false
      · exact ⟨base f i hi,base_supported f i hi,base_true f i hi,fun _ => hbj⟩
      · have hbjt : base f i hi j=true := by cases h : base f i hi j <;> simp_all
        refine ⟨GeneralEOPairedFamilyExtractionSupport.xor (base f i hi) w,hx _ _ (base_supported f i hi) hw,?_,?_⟩
        · simp [GeneralEOPairedFamilyExtractionSupport.xor,base_true,hwif]
        · intro _; simp [GeneralEOPairedFamilyExtractionSupport.xor,hbjt,hwjt]

def separator (i : Fin n) (hi : Active f i) (j : Fin n) : Fin n → Bool :=
  Classical.choose (separator_exists f hx i hi j)

theorem separator_spec (i : Fin n) (hi : Active f i) (j : Fin n) :
    f (separator f hx i hi j)≠0 ∧ separator f hx i hi j i=true ∧
      (¬Same f i j → separator f hx i hi j j=false) :=
  Classical.choose_spec (separator_exists f hx i hi j)

def intersection (b : Fin n → Bool) (ws : List (Fin n → Bool)) : Fin n → Bool :=
  fun j => b j && ws.all (fun w => w j)

theorem intersection_nil (b : Fin n → Bool) : intersection b []=b := by funext j; simp [intersection]
theorem intersection_cons (b w : Fin n → Bool) (ws : List (Fin n → Bool)) :
    intersection b (w::ws)=meet w (intersection b ws) := by
  funext j
  simp only [intersection,List.all_cons,meet]
  cases b j <;> cases w j <;> rfl

theorem intersection_supported (hm : MeetClosed f) (b : Fin n → Bool) (hb : f b≠0)
    (ws : List (Fin n → Bool)) (hw : ∀w∈ws,f w≠0) : f (intersection b ws)≠0 := by
  induction ws with
  | nil => simpa only [intersection_nil] using hb
  | cons w ws ih =>
    rw [intersection_cons]
    exact hm _ _ (hw w (by simp)) (ih (fun v hv => hw v (by simp [hv])))

def axis (i : Fin n) : Fin n → Bool := fun j => decide (Same f i j)

theorem axis_eq_intersection (i : Fin n) (hi : Active f i) :
    axis f i=intersection (base f i hi) (List.ofFn (separator f hx i hi)) := by
  funext j
  by_cases hs : Same f i j
  · have hb : base f i hi j=true := (hs _ (base_supported f i hi)).symm.trans (base_true f i hi)
    have hw : (List.ofFn (separator f hx i hi)).all (fun w => w j)=true := by
      apply List.all_eq_true.mpr
      intro w hw
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hw
      exact (hs _ (separator_spec f hx i hi k).1).symm.trans (separator_spec f hx i hi k).2.1
    simp [axis,hs,intersection,hb,hw]
  · have hw : (List.ofFn (separator f hx i hi)).all (fun w => w j)=false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      have he := List.all_eq_true.mp hh (separator f hx i hi j) (List.mem_ofFn.mpr ⟨j,rfl⟩)
      rw [(separator_spec f hx i hi j).2.2 hs] at he
      contradiction
    simp [axis,hs,intersection,hw]

include hx in
theorem axis_supported (hm : MeetClosed f) (i : Fin n) (hi : Active f i) : f (axis f i)≠0 := by
  rw [axis_eq_intersection f hx i hi]
  apply intersection_supported f hm _ (base_supported f i hi)
  intro w hw
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
  exact (separator_spec f hx i hi j).1

def join (u v : Fin n → Bool) : Fin n → Bool := fun j => u j || v j

include hx in
theorem join_supported (hm : MeetClosed f) (u v : Fin n → Bool) (hu : f u≠0) (hv : f v≠0) :
    f (join u v)≠0 := by
  have he : join u v=GeneralEOPairedFamilyExtractionSupport.xor (GeneralEOPairedFamilyExtractionSupport.xor u v) (meet u v) := by
    funext j; simp only [join,GeneralEOPairedFamilyExtractionSupport.xor,meet]; cases u j <;> cases v j <;> rfl
  rw [he]
  exact hx _ _ (hx _ _ hu hv) (hm _ _ hu hv)

def unionWords (ws : List (Fin n → Bool)) : Fin n → Bool := fun j => ws.any (fun w => w j)

include hx in
theorem unionWords_supported (h0 : f origin≠0) (hm : MeetClosed f)
    (ws : List (Fin n → Bool)) (hw : ∀w∈ws,f w≠0) : f (unionWords ws)≠0 := by
  induction ws with
  | nil => exact h0
  | cons w ws ih =>
    exact join_supported f hx hm w (unionWords ws) (hw w (by simp))
      (ih (fun v hv => hw v (by simp [hv])))

include hx in
/-- Complete support description: inactive coordinates are zero and
coordinates with the same support column agree. -/
theorem support_iff (h0 : f origin≠0) (hm : MeetClosed f) (x : Fin n → Bool) :
    f x≠0 ↔ (∀i,x i=true → Active f i) ∧ (∀i j,Same f i j → x i=x j) := by
  constructor
  · intro h
    exact ⟨fun i hi => ⟨x,h,hi⟩,fun i j hs => hs x h⟩
  · rintro ⟨ha,he⟩
    let ws := List.ofFn (fun i : Fin n => if x i then axis f i else origin)
    have hw : ∀w∈ws,f w≠0 := by
      intro w hw
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hw
      by_cases hi : x i=true
      · simpa only [hi,ite_true] using axis_supported f hx hm i (ha i hi)
      · simp only [hi]
        exact h0
    have hwx : unionWords ws=x := by
      funext j
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hj
        obtain ⟨w,hw,hwj⟩ := List.any_eq_true.mp hj
        obtain ⟨i,hi⟩ := List.mem_ofFn.mp hw
        subst w
        by_cases hxi : x i=true
        · have hs : Same f i j := by simpa only [hxi,ite_true,axis,decide_eq_true_eq] using hwj
          exact (he i j hs).symm.trans hxi
        · simp [hxi,origin] at hwj
      · intro hxj
        apply List.any_eq_true.mpr
        refine ⟨axis f j,List.mem_ofFn.mpr ⟨j,by simp [hxj]⟩,?_⟩
        simp [axis,same_refl]
    rw [←hwx]
    exact unionWords_supported f hx h0 hm ws hw

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionComponents
