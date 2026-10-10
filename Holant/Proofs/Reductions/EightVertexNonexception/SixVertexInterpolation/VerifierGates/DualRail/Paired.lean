import Holant.Proofs.Reductions.EightVertexNonexception.SixVertexInterpolation.VerifierGates.Clauses


namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.DualRail
open Holant

/-- Ordered pairs are (0,3), (1,4), (2,5). False is 01 and true is 10. -/
def encode (x : Fin 3 → Bool) : Fin 6 → Bool :=
  ![x 0,x 1,x 2,!x 0,!x 1,!x 2]
def decode (t : Fin 6 → Bool) : Fin 3 → Bool := ![t 0,t 1,t 2]
def Balanced (t : Fin 6 → Bool) : Prop :=
  t 3 = !t 0 ∧ t 4 = !t 1 ∧ t 5 = !t 2
instance (t : Fin 6 → Bool) : Decidable (Balanced t) := by unfold Balanced; infer_instance

theorem six_eq_iff (x y : Fin 6 → Bool) :
    x = y ↔ x 0=y 0 ∧ x 1=y 1 ∧ x 2=y 2 ∧ x 3=y 3 ∧ x 4=y 4 ∧ x 5=y 5 := by
  constructor
  · intro h
    exact ⟨congrFun h 0,congrFun h 1,congrFun h 2,
      congrFun h 3,congrFun h 4,congrFun h 5⟩
  · rintro ⟨h0,h1,h2,h3,h4,h5⟩
    funext i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5

theorem decode_encode (x : Fin 3 → Bool) : decode (encode x)=x := by
  funext i
  fin_cases i <;> rfl
theorem encode_balanced (x : Fin 3 → Bool) : Balanced (encode x) := by
  exact ⟨rfl,rfl,rfl⟩
theorem balanced_iff_encode (t : Fin 6 → Bool) : Balanced t ↔ t=encode (decode t) := by
  simp [Balanced,six_eq_iff,encode,decode,Fin.reduceFinMk]

/-- The exact six-port value after joining the two genuine fourth ports. -/
def separated {K : Type*} [CommSemiring K] (a b : Fin 3 → K) : Signature K 6 := fun t =>
  oneClause (a 0) (a 1) (a 2) ![t 0,t 1,t 2,true] *
    twoClause (b 0) (b 1) (b 2) ![t 3,t 4,t 5,false]

theorem encoded_value {K : Type*} [CommSemiring K] (a b : Fin 3 → K) (x : Fin 3 → Bool) :
    separated a b (encode x) =
      match x 0,x 1,x 2 with
      | true,false,false => a 0*b 0
      | false,true,false => a 1*b 1
      | false,false,true => a 2*b 2
      | _,_,_ => 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [separated,encode,oneClause,twoClause,h0,h1,h2]

/-- All words, including the invalid pair words, are covered by this relation. -/
theorem full_support {K : Type*} [Field K] (a b : Fin 3 → K)
    (ha : ∀ i,a i≠0) (hb : ∀ i,b i≠0) (t : Fin 6 → Bool) :
    separated a b t≠0 ↔ exactlyOne ![t 0,t 1,t 2] ∧ exactlyTwo ![t 3,t 4,t 5] := by
  rw [separated,mul_ne_zero_iff,
    one_support _ _ _ (ha 0) (ha 1) (ha 2),
    two_support _ _ _ (hb 0) (hb 1) (hb 2)]
  simp

theorem encoded_support {K : Type*} [Field K] (a b : Fin 3 → K)
    (ha : ∀ i,a i≠0) (hb : ∀ i,b i≠0) (x : Fin 3 → Bool) :
    separated a b (encode x)≠0 ↔ exactlyOne x := by
  rw [encoded_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp [exactlyOne,triple_eq_iff,h0,h1,h2,ha,hb]

def invalid : Fin 6 → Bool := ![true,false,false,true,true,false]
theorem invalid_unbalanced : ¬ Balanced invalid := by simp [Balanced,invalid]
theorem invalid_value {K : Type*} [CommSemiring K] (a b : Fin 3 → K) :
    separated a b invalid=a 0*b 2 := rfl
theorem invalid_nonzero {K : Type*} [Field K] (a b : Fin 3 → K)
    (ha : a 0≠0) (hb : b 2≠0) : separated a b invalid≠0 := by
  rw [invalid_value]
  exact mul_ne_zero ha hb

/-- The ONE side cannot support both a word and its bitwise complement.
This obstruction survives every boundary permutation or rail orientation. -/
theorem complementary_vanish {K : Type*} [CommSemiring K] (a b : Fin 3 → K)
    (t : Fin 6 → Bool) (ht : separated a b t≠0) :
    separated a b (fun i => !t i)=0 := by
  cases h0 : t 0 <;> cases h1 : t 1 <;> cases h2 : t 2 <;>
    simp [separated,oneClause,h0,h1,h2] at ht ⊢
theorem complementary_product_zero {K : Type*} [CommSemiring K] (a b : Fin 3 → K)
    (t : Fin 6 → Bool) : separated a b t*separated a b (fun i => !t i)=0 := by
  by_cases h : separated a b t=0
  · rw [h,zero_mul]
  · rw [complementary_vanish a b t h,mul_zero]

/-- The intended total relation also rejects every invalid pair encoding. -/
def copy {K : Type*} [Zero K] [One K] : Signature K 6 := fun t =>
  if Balanced t ∧ t 0=t 1 ∧ t 1=t 2 then 1 else 0
def nand {K : Type*} [Zero K] [One K] : Signature K 6 := fun t =>
  if Balanced t ∧ t 2 = !(t 0 && t 1) then 1 else 0

theorem copy_encoded {K : Type*} [Zero K] [One K] (x : Fin 3 → Bool) :
    copy (K:=K) (encode x) = if x 0=x 1 ∧ x 1=x 2 then 1 else 0 := by
  simp [copy,Balanced,encode]
theorem nand_encoded {K : Type*} [Zero K] [One K] (x : Fin 3 → Bool) :
    nand (K:=K) (encode x) = if x 2 = !(x 0 && x 1) then 1 else 0 := by
  simp [nand,Balanced,encode]
theorem copy_invalid {K : Type*} [Zero K] [One K] : copy (K:=K) invalid=0 := by
  simp only [copy,invalid_unbalanced,false_and,if_false]
theorem nand_invalid {K : Type*} [Zero K] [One K] : nand (K:=K) invalid=0 := by
  simp only [nand,invalid_unbalanced,false_and,if_false]

/-- Missing encoded 000 prevents every projective COPY identification,
independently of the three original clause weights. -/
theorem not_scaled_copy {K : Type*} [Field K] (a b : Fin 3 → K) (s : K) (hs : s≠0) :
    separated a b ≠ fun t => s*copy t := by
  intro h
  have ht := congrFun h (encode ![false,false,false])
  exact hs (by simpa [separated,encode,oneClause,twoClause,copy,Balanced] using ht.symm)

/-- Encoded 110 is a valid NAND input/output tuple, but its ONE side vanishes. -/
theorem not_scaled_nand {K : Type*} [Field K] (a b : Fin 3 → K) (s : K) (hs : s≠0) :
    separated a b ≠ fun t => s*nand t := by
  intro h
  have ht := congrFun h (encode ![true,true,false])
  exact hs (by simpa [separated,encode,oneClause,twoClause,nand,Balanced] using ht.symm)

end Holant.LocalDrafts.Hardness.EightVertexNonexception.SixVertexInterpolation.VerifierGates.DualRail
