import Holant.Proofs.Hardness.EONegativeCompletions
import Holant.Proofs.Hardness.DenseEOUnitLocal
import Holant.Tractable.SymmetricBinaryPullback.Product
import Holant.Complexity.BinaryInterpolation.BinaryFactors

/-! Literal EOTract certificates for small EO supports. The product-class
witnesses are actual unary/equality formulas for every original pairing. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
open scoped BigOperators
namespace B
export Holant.Tractable.SymmetricBinaryPullback (table ProductShape product_of_monomial)
end B
set_option backward.isDefEq.respectTransparency false

def support {n : ℕ} (f : Signature AlgebraicComplex n) : Finset (Fin n→Bool) := by
  classical
  exact Finset.univ.filter fun x=>f x≠0

@[simp] theorem mem_support {n : ℕ} (f : Signature AlgebraicComplex n) (x : Fin n→Bool) :
    x∈support f ↔ f x≠0 := by
  classical
  simp [support]

theorem binary_singular (E : Kernel AlgebraicComplex) (hd : Matrix.det E=0) :
    Product (Holant.Tractable.kernelSignature E) := by
  by_cases he : E=0
  · subst E
    exact product_zero 2
  · obtain ⟨u,v,_,_,huv⟩ := Holant.Complexity.BinaryInterpolation.singular_binary_factors E he hd
    have hf : Holant.Tractable.kernelSignature E=(fun x => u (x 0)*v (x 1)) := by
      funext x
      change E (x 0) (x 1)=_
      rw [huv]
      rfl
    rw [hf]
    exact (product_unary (0 : Fin 2) u).mul (product_unary (1 : Fin 2) v)

theorem binary_of_shape (f : Signature AlgebraicComplex 2) (h : B.ProductShape (B.table f)) : Product f := by
  have he : Holant.Tractable.kernelSignature (B.table f)=f := by
    funext x
    change f ![x 0,x 1]=f x
    congr 1
    funext i
    fin_cases i <;> rfl
  rw [←he]
  rcases h with h|h|h
  · exact B.product_of_monomial (.inl h)
  · exact B.product_of_monomial (.inr h)
  · apply binary_singular
    rw [Holant.Complexity.BinaryInterpolation.det_entries]
    exact sub_eq_zero.mpr h

theorem binary_small (f : Signature AlgebraicComplex 2) (h : (support f).card≤2) : Product f := by
  classical
  apply binary_of_shape
  have hu : (Finset.univ : Finset (Fin 2→Bool))=
      {![false,false],![false,true],![true,false],![true,true]} := by decide
  by_cases h0 : f ![false,false]=0 <;> by_cases h1 : f ![false,true]=0 <;>
    by_cases h2 : f ![true,false]=0 <;> by_cases h3 : f ![true,true]=0
  all_goals simp_all [support,hu,Finset.filter_insert,Finset.filter_singleton,B.ProductShape,B.table]

/-- Every pairing word retains the original first incidence of each pair. -/
theorem word_injective {n : ℕ} (p : OrientedPerfectPairing n) : Function.Injective p.word := by
  intro a b hab
  funext i
  have h := congrFun hab (p.ports (i,false))
  simpa only [OrientedPerfectPairing.word,Equiv.symm_apply_apply,Bool.false_eq_true,ite_false] using h

theorem restriction_card (M : Signature AlgebraicComplex 4) (p : OrientedPerfectPairing 4) :
    (support (p.restrict M)).card≤(support M).card := by
  classical
  have hi : (support (p.restrict M)).image p.word ⊆ support M := by
    intro x hx
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hx
    exact (mem_support M _).mpr ((mem_support (p.restrict M) _).mp hz)
  calc
    (support (p.restrict M)).card=((support (p.restrict M)).image p.word).card :=
      (Finset.card_image_of_injective _ (word_injective p)).symm
    _≤(support M).card := Finset.card_le_card hi

theorem pairing_small (M : Signature AlgebraicComplex 4) (h : (support M).card≤2)
    (p : OrientedPerfectPairing 4) : Product (p.restrict M) := by
  have hc := EONegativeCompletions.pairing_count p
  have hh := (restriction_card M p).trans h
  rcases p with ⟨n,ports⟩
  dsimp only at hc
  subst n
  exact binary_small _ hh

theorem small_triples (M : Signature AlgebraicComplex 4) (h : (support M).card≤2)
    (a b c : Fin 4→Bool) (ha : M a≠0) (hb : M b≠0) (hc : M c≠0) :
    a=b ∨ a=c ∨ b=c := by
  classical
  by_contra hn
  push_neg at hn
  have hs : ({a,b,c} : Finset (Fin 4→Bool))⊆support M := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl|rfl|rfl
    · exact (mem_support M _).mpr ha
    · exact (mem_support M _).mpr hb
    · exact (mem_support M _).mpr hc
  have h3 : ({a,b,c} : Finset (Fin 4→Bool)).card=3 := by simp [hn.1,hn.2.1,hn.2.2]
  have := Finset.card_le_card hs
  omega

theorem repeated_xor : ∀a b c : Fin 4→Bool, a=b ∨ a=c ∨ b=c →
    tripleXor a b c=a ∨ tripleXor a b c=b ∨ tripleXor a b c=c := by decide

theorem support_small (M : Signature AlgebraicComplex 4) (h : (support M).card≤2) :
    EONegativeWitness.Supports .positive ⟨4,M⟩ := by
  intro a b c ha hb hc
  left
  rcases repeated_xor a b c (small_triples M h a b c ha hb hc) with hx|hx|hx
  · simpa only [hx] using ha
  · simpa only [hx] using hb
  · simpa only [hx] using hc

theorem small_tract (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (h : (support M).card≤2) : EOTract {⟨4,M⟩} := by
  refine ⟨by simp, ?_, .positive, .product, ?_, ?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    refine ⟨⟨2,rfl⟩,?_⟩
    intro x hx
    change 2*weight x≠4 at hx
    exact he x (by omega)
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact support_small M h
  · intro g hg p
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact pairing_small M h p

/-- One original port is fixed throughout the support, with arbitrary weights. -/
def FixedPort (M : Signature AlgebraicComplex 4) (j : Fin 4) (bit : Bool) : Prop :=
  ∀x, M x≠0 → x j=bit

private theorem fixed_bits : ∀j : Fin 4, ∀bit : Bool, ∀a b c : Fin 4→Bool,
    weight a=2 ∧ a j=bit → weight b=2 ∧ b j=bit → weight c=2 ∧ c j=bit →
      tripleXor a b c=a ∨ tripleXor a b c=b ∨ tripleXor a b c=c ∨
        0 < (if bit then (1 : ℤ) else -1)*Holant.charge (tripleXor a b c) := by
  intro j bit
  fin_cases j <;> cases bit <;> decide

private theorem pinned_count : ∀j : Fin 2, ∀orient bit : Bool,
    (Finset.univ.filter (fun z : Fin 2→Bool => (if orient then !(z j) else z j)=bit)).card=2 := by decide

theorem pairing_fixed (M : Signature AlgebraicComplex 4) (j : Fin 4) (bit : Bool)
    (h : FixedPort M j bit) (p : OrientedPerfectPairing 4) : Product (p.restrict M) := by
  classical
  have hc := EONegativeCompletions.pairing_count p
  rcases p with ⟨n,ports⟩
  dsimp only at hc
  subst n
  apply binary_small
  let q := ports.symm j
  have hs : support ((OrientedPerfectPairing.mk 2 ports).restrict M) ⊆
      Finset.univ.filter (fun z : Fin 2→Bool => (if q.2 then !(z q.1) else z q.1)=bit) := by
    intro z hz
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    have hz' := (mem_support ((OrientedPerfectPairing.mk 2 ports).restrict M) z).mp hz
    exact h _ hz'
  have hh := Finset.card_le_card hs
  rw [pinned_count] at hh
  exact hh

theorem support_fixed (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (j : Fin 4) (bit : Bool) (h : FixedPort M j bit) :
    EONegativeWitness.Supports (EONegativeCompletions.sign bit) ⟨4,M⟩ := by
  intro a b c ha hb hc
  have ha' : weight a=2 := by by_contra hn; exact ha (he a hn)
  have hb' : weight b=2 := by by_contra hn; exact hb (he b hn)
  have hc' : weight c=2 := by by_contra hn; exact hc (he c hn)
  rcases fixed_bits j bit a b c ⟨ha',h a ha⟩ ⟨hb',h b hb⟩ ⟨hc',h c hc⟩ with hx|hx|hx|hx
  · exact Or.inl (by simpa only [hx] using ha)
  · exact Or.inl (by simpa only [hx] using hb)
  · exact Or.inl (by simpa only [hx] using hc)
  · right
    cases bit <;> simpa [EONegativeCompletions.sign,EOSign.value] using hx

/-- Weighted stars and triangles satisfy the actual shared-sign/product criterion. -/
theorem fixed_tract (M : Signature AlgebraicComplex 4) (he : DenseEOUnitLocal.EOSupport M)
    (j : Fin 4) (bit : Bool) (h : FixedPort M j bit) : EOTract {⟨4,M⟩} := by
  refine ⟨by simp, ?_, EONegativeCompletions.sign bit, .product, ?_, ?_⟩
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    refine ⟨⟨2,rfl⟩,?_⟩
    intro x hx
    change 2*weight x≠4 at hx
    exact he x (by omega)
  · intro g hg
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact support_fixed M he j bit h
  · intro g hg p
    rcases Set.mem_singleton_iff.mp hg with rfl
    exact pairing_fixed M j bit h p

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternarySparseTract
