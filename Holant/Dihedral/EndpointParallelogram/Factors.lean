import Holant.Dihedral.EndpointParallelogram.Source

/-! A literal product of nonsingular monomial binary factors supplies the
actual-card matching witness used by the endpoint test. Arbitrary original
ordered ports and both monomial parities are retained. -/
namespace Holant.Dihedral.EndpointParallelogram
open Holant

variable {r n : ℕ}

def Pairing.ofPorts (p : (Fin r × Bool) ≃ Fin n) : Pairing (Fin n) where
  mate i := p ((p.symm i).1,!(p.symm i).2)
  involutive := by
    intro i
    simp only [Equiv.symm_apply_apply,Bool.not_not,Prod.mk.eta,Equiv.apply_symm_apply]
  fixed_free := by
    intro i h
    have hh := congrArg (fun j => (p.symm j).2) h
    simp only [Equiv.symm_apply_apply] at hh
    cases hb : (p.symm i).2 <;> simp [hb] at hh

theorem Pairing.ofPorts_code (p : (Fin r × Bool) ≃ Fin n) (x : Fin n → ZMod 2) :
    x ∈ (Pairing.ofPorts p).code ↔ ∀ e, x (p (e,false)) = x (p (e,true)) := by
  constructor
  · intro h e
    have hh := h (p (e,true))
    simpa only [ofPorts,Equiv.symm_apply_apply,Bool.not_true] using hh
  · intro h i
    obtain ⟨⟨e,b⟩,rfl⟩ := p.surjective i
    cases b
    · simpa only [ofPorts,Equiv.symm_apply_apply,Bool.not_false] using (h e).symm
    · simpa only [ofPorts,Equiv.symm_apply_apply,Bool.not_true] using h e

def matchingOffset (p : (Fin r × Bool) ≃ Fin n) (parity : Fin r → ZMod 2) : Fin n → ZMod 2 :=
  fun i => if (p.symm i).2 then parity (p.symm i).1 else 0

theorem matching_coset_iff (p : (Fin r × Bool) ≃ Fin n) (parity : Fin r → ZMod 2)
    (x : Fin n → ZMod 2) :
    x ∈ coset (Pairing.ofPorts p).code (matchingOffset p parity) ↔
      ∀ e, x (p (e,true)) = x (p (e,false)) + parity e := by
  simp only [coset,Set.mem_setOf_eq,Pairing.ofPorts_code,Pi.add_apply,
    matchingOffset,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false,ite_true,add_zero]
  constructor
  · intro h e
    have hh := congrArg (· + parity e) (h e)
    simpa only [add_assoc,ZModModule.add_self,add_zero] using hh.symm
  · intro h e
    rw [h e,add_assoc,ZModModule.add_self,add_zero]

variable {K : Type*} [Field K]

/-- Each literal binary factor has its two arbitrary nonzero entries on the
chosen diagonal or antidiagonal. This is an exact coefficient product. -/
def monomialProduct (p : (Fin r × Bool) ≃ Fin n) (parity : Fin r → ZMod 2)
    (w : Fin r → Bool → K) (κ : K) : Signature K n := fun x =>
  κ * ∏ e, if bitEquiv (x (p (e,true))) = bitEquiv (x (p (e,false))) + parity e
    then w e (x (p (e,false))) else 0

theorem monomialProduct_matching (p : (Fin r × Bool) ≃ Fin n)
    (parity : Fin r → ZMod 2) (w : Fin r → Bool → K) (κ : K)
    (hw : ∀ e b, w e b ≠ 0) (hκ : κ ≠ 0) :
    CardMatching (monomialProduct p parity w κ) (Pairing.ofPorts p) (matchingOffset p parity) := by
  intro x
  rw [matching_coset_iff]
  simp only [monomialProduct,mul_ne_zero_iff,hκ,true_and,Finset.prod_ne_zero_iff,
    Finset.mem_univ,forall_const]
  have hx (i : Fin n) : bitEquiv ((bitsEquiv (Fin n)).symm x i) = x i := by
    exact bitEquiv.apply_symm_apply (x i)
  simp only [hx,hκ,true_and]
  constructor
  · intro hh e
    by_contra hn
    have he := hh.2 e
    simp only [hn,ite_false,ne_eq,not_true_eq_false] at he
  · intro hh
    refine ⟨hκ,fun e => ?_⟩
    rw [if_pos (hh e)]
    exact hw _ _

/-- The matching-witness input in the public source theorem follows from an
actual factorization of that same sampled card, with no factor gadget access. -/
theorem cardMatching_of_factorization (f : Signature K n)
    (p : (Fin r × Bool) ≃ Fin n) (parity : Fin r → ZMod 2)
    (w : Fin r → Bool → K) (κ : K) (hw : ∀ e b, w e b ≠ 0) (hκ : κ ≠ 0)
    (hf : f = monomialProduct p parity w κ) :
    CardMatching f (Pairing.ofPorts p) (matchingOffset p parity) :=
  hf ▸ monomialProduct_matching p parity w κ hw hκ

/-- Full source specialization from the two actual monomial product cards.
Their matching compatibility is derived; neither a direction equality nor the
parallelogram condition is among the hypotheses. -/
theorem source_endpoint_from_products
    (F : SignatureFamily K) (W : EdgeKind)
    (q : Signature K (n+2)) (ports : Equiv.Perm (Fin (n+2)))
    (L : Submodule (ZMod 2) (Fin n → ZMod 2)) (a b c d : Fin n → ZMod 2)
    (hA : fullCoset (slice q ports false false) L a)
    (hB : fullCoset (slice q ports false true) L b)
    (hC : fullCoset (slice q ports true false) L c)
    (hD : fullCoset (slice q ports true true) L d)
    (hE : a+d ∉ L) (hO : b+c ∉ L)
    (t s κE κO : K) (ht : t ≠ 0) (hs : s ≠ 0) (hκE : κE ≠ 0) (hκO : κO ≠ 0)
    (pE pO : (Fin r × Bool) ≃ Fin n) (parityE parityO : Fin r → ZMod 2)
    (wE wO : Fin r → Bool → K) (cE cO : K)
    (hwE : ∀ e b, wE e b ≠ 0) (hwO : ∀ e b, wO e b ≠ 0)
    (hcE : cE ≠ 0) (hcO : cO ≠ 0)
    (factorE : card q ports false t κE = monomialProduct pE parityE wE cE)
    (factorO : card q ports true s κO = monomialProduct pO parityO wO cO)
    (physicalE : Gadget.Realizes F W (card q ports false t κE))
    (physicalO : Gadget.Realizes F W (card q ports true s κO)) :
    (Pairing.ofPorts pE = Pairing.ofPorts pO ↔ a+b+c+d ∈ L) ∧
    card q ports false t κE ≠ 0 ∧ card q ports true s κO ≠ 0 ∧
    (a+b+c+d ∉ L →
      Gadget.Realizes F W (card q ports false t κE) ∧
      Gadget.Realizes F W (card q ports true s κO) ∧ Pairing.ofPorts pE ≠ Pairing.ofPorts pO) :=
  source_actual_card_endpoint_test F W q ports L a b c d hA hB hC hD hE hO
    t s κE κO ht hs hκE hκO (Pairing.ofPorts pE) (Pairing.ofPorts pO)
    (matchingOffset pE parityE) (matchingOffset pO parityO)
    (cardMatching_of_factorization _ pE parityE wE cE hwE hcE factorE)
    (cardMatching_of_factorization _ pO parityO wO cO hwO hcO factorO) physicalE physicalO

end Holant.Dihedral.EndpointParallelogram
