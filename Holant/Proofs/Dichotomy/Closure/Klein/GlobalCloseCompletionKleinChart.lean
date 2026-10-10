import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinDenseSeparated

/-! Actual parity/complement normalization for a dense standard-Klein q4.
A literal-I bit flip fixes parity; the actual Pauli skew representative fixes
the complementary sign. Both operations preserve their nonzero multipliers. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinChart
open Holant Holant.Tractable Holant.Algebraic Holant.Marked Holant.Marked.SupportAtlas
open Holant.Certificates.EqualityQuaternary
open Holant.LocalDrafts.Hardness.EightVertexNonexception hiding Word
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.OpenNetworkComposition
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal Z)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false

def J : Kernel AlgebraicComplex := fun b c=>if b= !c then (if b then -1 else 1) else 0

def signFirst (q : Signature AlgebraicComplex 4) : Signature AlgebraicComplex 4 :=
  fun x=>(if x 0 then -1 else 1)*q x

private theorem sign_actual (F : SignatureFamily AlgebraicComplex) (q : Signature AlgebraicComplex 4)
    (hq : Gadget.RealizesUpTo F .disequality q)
    (hj : Gadget.RealizesUpTo F .disequality (kernelSignature J)) :
    Gadget.RealizesUpTo F .disequality (signFirst q) := by
  obtain ⟨c,hc,hq⟩ := hq
  obtain ⟨d,hd,hj⟩ := hj
  have ha := realizes_splice F _ _ hq hj 0
  refine ⟨c*d,mul_ne_zero hc hd,?_⟩
  convert ha using 1
  funext x
  have update : Function.update x 0 (x 0)=x := Function.update_eq_self _ _
  cases hx : x 0
  all_goals
    rw [hx] at update
    simp [spliceTensor,Signature.disequality,J,kernelSignature,signFirst,hx,update]
    ring

private theorem flip_actual (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (q : Signature AlgebraicComplex 4) (actual : Gadget.RealizesUpTo F .disequality q) (mask : Word) :
    Gadget.RealizesUpTo F .disequality (Flip.value q mask) := by
  obtain ⟨c,hc,actual⟩ := actual
  refine ⟨c,hc,?_⟩
  exact Flip.actual F _ actual (Gadget.realizes_of_mem _ .disequality _ hI) mask

theorem normal_of_rules (q : Signature AlgebraicComplex 4) (even : EvenSupport q)
    (complementary : ∀x,q (complement x)=q x) :
    q=T.normal (entries q).a (entries q).b (entries q).c (entries q).d := by
  have hx := complementary ![false,false,false,false]
  have hy := complementary ![false,false,true,true]
  have hz := complementary ![false,true,false,true]
  have hw := complementary ![false,true,true,false]
  have cx : (entries q).x=(entries q).a := by
    change q ![true,true,true,true]=_
    trans q (complement ![false,false,false,false])
    · apply congrArg q
      funext i
      fin_cases i <;> rfl
    · exact hx
  have cy : (entries q).y=(entries q).b := by
    change q ![true,true,false,false]=_
    trans q (complement ![false,false,true,true])
    · apply congrArg q
      funext i
      fin_cases i <;> rfl
    · exact hy
  have cz : (entries q).z=(entries q).c := by
    change q ![true,false,true,false]=_
    trans q (complement ![false,true,false,true])
    · apply congrArg q
      funext i
      fin_cases i <;> rfl
    · exact hz
  have cw : (entries q).w=(entries q).d := by
    change q ![true,false,false,true]=_
    trans q (complement ![false,true,true,false])
    · apply congrArg q
      funext i
      fin_cases i <;> rfl
    · exact hw
  conv_lhs => rw [←table_entries q even]
  unfold T.normal
  congr 1
  apply Entries.ext <;> first | rfl | assumption

/-- Only actual I and J are used to choose an even complementary normal row. -/
theorem dense_normal (F : SignatureFamily AlgebraicComplex) (hI : RetainsIdentity F)
    (hj : Gadget.RealizesUpTo F .disequality (kernelSignature J))
    (q : Signature AlgebraicComplex 4) (actual : Gadget.RealizesUpTo F .disequality q)
    (p : Bool) (full : ∀x,q x≠0 ↔ parity x=p)
    (sign : AlgebraicComplex) (hs : sign=1 ∨ sign= -1)
    (complementary : ∀x,q (complement x)=sign*q x) :
    ∃a b c d : AlgebraicComplex,a≠0 ∧ b≠0 ∧ c≠0 ∧ d≠0 ∧
      Gadget.RealizesUpTo F .disequality (T.normal a b c d) := by
  let mask : Word := ![p,false,false,false]
  have pm : parity mask=p := by cases p <;> rfl
  let f := Flip.value q mask
  have fa := flip_actual F hI q actual mask
  have ff : ∀x,f x≠0 ↔ parity x=false := by
    intro x
    change q (xorWord x mask)≠0 ↔ _
    rw [full,parity_xorWord,pm]
    cases parity x <;> cases p <;> decide
  have fc : ∀x,f (complement x)=sign*f x := by
    intro x
    change q (xorWord (complement x) mask)=sign*q (xorWord x mask)
    have flip : xorWord (complement x) mask=complement (xorWord x mask) := by
      funext i
      cases hx : x i <;> cases hm : mask i <;> simp [xorWord,complement,hx,hm]
    rw [flip]
    exact complementary _
  have normalExists : ∀f : Signature AlgebraicComplex 4,
      Gadget.RealizesUpTo F .disequality f → (∀x,f x≠0 ↔ parity x=false) →
      (∀x,f (complement x)=f x) →
      ∃a b c d : AlgebraicComplex,a≠0 ∧ b≠0 ∧ c≠0 ∧ d≠0 ∧
        Gadget.RealizesUpTo F .disequality (T.normal a b c d) := by
    intro f actual full comp
    have even : EvenSupport f := by
      intro x odd
      by_contra live
      have hp := (full x).mp live
      have one : weight x%2=1 := by have bound := Nat.mod_lt (weight x) (by decide : 0<2); omega
      have trueParity := (parity_weight x).mpr one
      rw [hp] at trueParity
      contradiction
    have form := normal_of_rules f even comp
    refine ⟨(entries f).a,(entries f).b,(entries f).c,(entries f).d,
      (full _).mpr (by decide),(full _).mpr (by decide),
      (full _).mpr (by decide),(full _).mpr (by decide),?_⟩
    rwa [←form]
  rcases hs with rfl|rfl
  · exact normalExists f fa ff (fun x=>by simpa only [one_mul] using fc x)
  · apply normalExists (signFirst f) (sign_actual F f fa hj)
    · intro x
      have hn : (if x 0 then (-1 : AlgebraicComplex) else 1)≠0 := by cases x 0 <;> norm_num
      constructor
      · intro live
        exact (ff x).mp (mul_ne_zero_iff.mp live).2
      · intro par
        exact mul_ne_zero hn ((ff x).mpr par)
    · intro x
      simp only [signFirst,complement,fc]
      by_cases hx : x 0=true <;> simp [hx,complement] <;> ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinChart
end
