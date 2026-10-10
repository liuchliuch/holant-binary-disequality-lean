import Holant.Proofs.Hardness.EONegativeWitness
import Holant.Proofs.Hardness.SparseUnitValue

/-! A genuine incompatible mixed EO family. Each four-port signature is
individually EOTract, in the SAME product class but with OPPOSITE support
signs. Their union fails the literal criterion. These are the minimal ordered
EO completions of native ternary ONE and TWO, with one appended fixed bit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeCompletions
open Holant Holant.Tractable
open scoped BigOperators
namespace W
export EONegativeWitness (Supports Pairings Obstruction pair_not_tract)
end W

variable {K : Type*} [Field K]

theorem weight_four (x : Fin 4 → Bool) : weight x =
    (if x 0 then 1 else 0) + (if x 1 then 1 else 0) +
      (if x 2 then 1 else 0) + (if x 3 then 1 else 0) := Fin.sum_univ_four _

def literal (bit : Bool) : Signature K 4 :=
  fun x => if weight x = 2 ∧ x 3 = bit then 1 else 0

@[simp] theorem support (bit : Bool) (x : Fin 4 → Bool) :
    literal (K:=K) bit x ≠ 0 ↔ weight x=2 ∧ x 3=bit := by
  simp [literal]

theorem central (bit : Bool) : Signature.CentralSupport (literal (K:=K) bit) := by
  intro x hx
  have h : weight x≠2 := by omega
  simp [literal,h]

/-- Original three ports retain their order; only the final fixed port is new. -/
theorem true_one (x : Fin 4 → Bool) :
    literal (K:=K) true x =
      if x 3=true then SparseUnitLocal.ONE ![x 0,x 1,x 2] else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [literal, weight_four, SparseUnitLocal.ONE, h0,h1,h2,h3]

theorem false_two (x : Fin 4 → Bool) :
    literal (K:=K) false x =
      if x 3=false then SparseUnitLocal.TWO ![x 0,x 1,x 2] else 0 := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [literal, weight_four, SparseUnitLocal.TWO, SparseUnitLocal.ONE, h0,h1,h2,h3]

/-- Finite combinatorial support fact; no class membership or hardness is
hidden in the table check. The true completion uses the positive sign. -/
theorem support_bits : ∀ bit : Bool, ∀ a b c : Fin 4 → Bool,
    weight a=2 ∧ a 3=bit → weight b=2 ∧ b 3=bit → weight c=2 ∧ c 3=bit →
      (weight (tripleXor a b c)=2 ∧ tripleXor a b c 3=bit) ∨
      0 < (if bit then (1 : ℤ) else -1) * Holant.charge (tripleXor a b c) := by
  decide

def sign (bit : Bool) : EOSign := if bit then .positive else .negative

theorem support_sign (bit : Bool) :
    W.Supports (sign bit) (⟨4,literal (K:=AlgebraicComplex) bit⟩) := by
  intro a b c ha hb hc
  have h := support_bits bit a b c ((support bit a).mp ha) ((support bit b).mp hb) ((support bit c).mp hc)
  rcases h with h | h
  · exact Or.inl ((support bit _).mpr h)
  · right
    cases bit <;> simpa [sign, EOSign.value] using h

/-- Any opposite-pair word has exactly one true bit per pair. -/
theorem word_weight {n : ℕ} (p : OrientedPerfectPairing n) (z : Fin p.count → Bool) :
    weight (p.word z)=p.count := by
  have h := Equiv.sum_comp p.ports (fun j => if p.word z j then (1 : ℕ) else 0)
  rw [weight, ←h, Fintype.sum_prod_type]
  simp only [OrientedPerfectPairing.word, Equiv.symm_apply_apply, Fintype.sum_bool,
    Bool.false_eq_true, ite_false, ite_true]
  calc
    (∑ i : Fin p.count, ((if !(z i) then 1 else 0) + if z i then 1 else 0)) =
      ∑ _ : Fin p.count, 1 := by
        apply Finset.sum_congr rfl
        intro i _
        cases z i <;> rfl
    _ = p.count := by simp

theorem pairing_count (p : OrientedPerfectPairing 4) : p.count=2 := by
  have h := Fintype.card_congr p.ports
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at h
  omega

/-- Every pairing restriction is literally one unary pin. No enumeration of
pairing witnesses, free pin gadget, or factor-extraction rule is assumed. -/
theorem restriction_unary (bit : Bool) (p : OrientedPerfectPairing 4) :
    p.restrict (literal (K:=AlgebraicComplex) bit) =
      fun z => if (if (p.ports.symm 3).2 then !(z (p.ports.symm 3).1)
        else z (p.ports.symm 3).1)=bit then 1 else 0 := by
  funext z
  simp [OrientedPerfectPairing.restrict,literal,word_weight,pairing_count,OrientedPerfectPairing.word]

theorem pairing_product (bit : Bool) (p : OrientedPerfectPairing 4) :
    Product (p.restrict (literal (K:=AlgebraicComplex) bit)) := by
  rw [restriction_unary]
  exact product_unary (p.ports.symm 3).1
    (fun b => if (if (p.ports.symm 3).2 then !b else b)=bit then 1 else 0)

theorem singleton_tract (bit : Bool) : EOTract {⟨4,literal (K:=AlgebraicComplex) bit⟩} := by
  refine ⟨by simp, ?_, sign bit, .product, ?_, ?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact ⟨⟨2,rfl⟩,central bit⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact support_sign bit
  · intro g hg p
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact pairing_product bit p

theorem true_not_negative :
    ¬W.Supports .negative (⟨4,literal (K:=AlgebraicComplex) true⟩) := by
  intro h
  have hh := h ![true,false,false,true] ![false,true,false,true] ![false,false,true,true]
    (by simp [literal,weight_four])
    (by simp [literal,weight_four])
    (by simp [literal,weight_four])
  norm_num [literal,weight_four,tripleXor,Holant.charge,weight_four,EOSign.value] at hh

theorem false_not_positive :
    ¬W.Supports .positive (⟨4,literal (K:=AlgebraicComplex) false⟩) := by
  intro h
  have hh := h ![false,true,true,false] ![true,false,true,false] ![true,true,false,false]
    (by simp [literal,weight_four])
    (by simp [literal,weight_four])
    (by simp [literal,weight_four])
  norm_num [literal,weight_four,tripleXor,Holant.charge,weight_four,EOSign.value] at hh

theorem pair_obstruction : W.Obstruction
    (⟨4,literal (K:=AlgebraicComplex) false⟩) (⟨4,literal (K:=AlgebraicComplex) true⟩) :=
  Or.inl ⟨false_not_positive,true_not_negative⟩

theorem pair_not_tract : ¬EOTract
    {⟨4,literal (K:=AlgebraicComplex) false⟩,⟨4,literal (K:=AlgebraicComplex) true⟩} :=
  W.pair_not_tract pair_obstruction

/-- Literal source completion correspondence, with the original ports first. -/
theorem complete_one : Signature.completeToEO (SparseUnitLocal.ONE : Signature K 3) 1 =
    (⟨4,literal true⟩ : AnySignature K) := by
  change (⟨4,Signature.completeWithOnes SparseUnitLocal.ONE 1⟩ : AnySignature K)=_
  apply congrArg (fun f : Signature K 4 => (⟨4,f⟩ : AnySignature K))
  funext x
  rw [true_one]
  have hr : (fun i : Fin 3 => x (Fin.castAdd 1 i)) = ![x 0,x 1,x 2] := by
    funext i
    fin_cases i <;> rfl
  simp only [Signature.completeWithOnes,Signature.tensor_apply,Signature.unaryPower_pointMass,hr]
  simp

/-- The complementary completion appends zero, at exactly the same last port. -/
theorem complete_two : Signature.completeToEO (SparseUnitLocal.TWO : Signature K 3) 2 =
    (⟨4,literal false⟩ : AnySignature K) := by
  change (⟨4,Signature.completeWithZeros SparseUnitLocal.TWO 2⟩ : AnySignature K)=_
  apply congrArg (fun f : Signature K 4 => (⟨4,f⟩ : AnySignature K))
  funext x
  rw [false_two]
  have hr : (fun i : Fin 3 => x (Fin.castAdd 1 i)) = ![x 0,x 1,x 2] := by
    funext i
    fin_cases i <;> rfl
  simp only [Signature.completeWithZeros,Signature.tensor_apply,Signature.unaryPower_pointMass,hr]
  simp

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EONegativeCompletions
