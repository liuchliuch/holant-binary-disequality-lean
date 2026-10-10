import Holant.Proofs.Closure.ClosureCompatibleAlignmentProductLines

/-! Coefficient-factor comparison across arbitrary actual edge enumerations.
The target residual edge type may differ from the source edge type; exact
matching incidence determines the index and endpoint reversal used below. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
open Holant Holant.Certificates.MatchingContractionClosure

variable {K P E D : Type} [Field K] [DecidableEq P]
variable [Fintype E] [DecidableEq E] [Fintype D] [DecidableEq D]

def incidenceIndex (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P) (e : E) : D :=
  (q.symm (p (e,false))).1

def incidenceReversed (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P) (e : E) : Bool :=
  (q.symm (p (e,false))).2

def incidenceFactor (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P)
    (B : D → Binary (K:=K)) (e : E) : Binary (K:=K) :=
  if incidenceReversed p q e then (B (incidenceIndex p q e)).transpose else B (incidenceIndex p q e)

theorem incidence_endpoint (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P)
    (same : ClosureMatchingMinor.mate p = ClosureMatchingMinor.mate q) (e : E) (b : Bool) :
    q (incidenceIndex p q e,b ^^ incidenceReversed p q e) = p (e,b) := by
  cases b
  · simpa only [incidenceIndex,incidenceReversed,Bool.false_xor,Prod.mk.eta]
      using q.apply_symm_apply (p (e,false))
  · have h := congrFun same (p (e,false))
    simp only [ClosureMatchingMinor.mate,Equiv.symm_apply_apply,Bool.not_false] at h
    simpa only [incidenceIndex,incidenceReversed,Bool.true_xor] using h.symm

theorem incidenceIndex_injective (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P)
    (same : ClosureMatchingMinor.mate p = ClosureMatchingMinor.mate q) :
    Function.Injective (incidenceIndex p q) := by
  intro e f equal
  have xorIdentity (a b : Bool) : ((a ^^ b) ^^ b) = a := by cases a <;> cases b <;> decide
  have h : p (e,false) = p (f,incidenceReversed p q e ^^ incidenceReversed p q f) := by
    rw [← incidence_endpoint p q same e false,
      ← incidence_endpoint p q same f (incidenceReversed p q e ^^ incidenceReversed p q f)]
    simp only [Bool.false_xor,xorIdentity,equal]
  exact congrArg Prod.fst (p.injective h)

theorem insertPair_swap (u v : P) (distinct : u ≠ v) (a b : Bool) (x : P → Bool) :
    insertPair u v a b x = insertPair v u b a x := by
  unfold insertPair
  exact Function.update_comm distinct a b x

theorem incidence_extract (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P)
    (same : ClosureMatchingMinor.mate p = ClosureMatchingMinor.mate q)
    (B : D → Binary (K:=K)) (c : K) (e : E) (a b : Bool) (x : P → Bool) :
    productValue q B c (insertPair (p (e,false)) (p (e,true)) a b x) =
      incidenceFactor p q B e a b *
        (c * ∏ j ∈ {incidenceIndex p q e}ᶜ,B j (x (q (j,false))) (x (q (j,true)))) := by
  rw [← incidence_endpoint p q same e false,← incidence_endpoint p q same e true]
  cases reversed : incidenceReversed p q e
  · simpa only [incidenceFactor,reversed,Bool.false_xor,Bool.true_xor,
      Bool.not_false,Bool.false_eq_true,ite_false] using
      product_extract_edge q B c (incidenceIndex p q e) a b x
  · have distinct : q (incidenceIndex p q e,true) ≠ q (incidenceIndex p q e,false) := by
      intro equal
      have h := congrArg Prod.snd (q.injective equal)
      cases h
    simp only [Bool.false_xor,reversed,Bool.true_xor,Bool.not_true,incidenceFactor,ite_true]
    rw [insertPair_swap _ _ distinct,product_extract_edge]
    rfl

/-- The exact ordered target factor line follows from the whole tensor, not
from a projective-line oracle or an arbitrary matching edge choice. -/
theorem equal_tensors_incidence_line (p : (E × Bool) ≃ P) (q : (D × Bool) ≃ P)
    (sameMatching : ClosureMatchingMinor.mate p = ClosureMatchingMinor.mate q)
    (A : E → Binary (K:=K)) (B : D → Binary (K:=K)) (c d : K)
    (nonzero : productValue p A c ≠ 0) (same : productValue p A c = productValue q B d) (e : E) :
    ∃ z : K,z ≠ 0 ∧ A e = z • incidenceFactor p q B e := by
  classical
  obtain ⟨x,hx⟩ : ∃ x,productValue p A c x ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact nonzero (funext hn)
  have inserted : insertPair (p (e,false)) (p (e,true))
      (x (p (e,false))) (x (p (e,true))) x = x := by simp [insertPair]
  let a := c * ∏ j ∈ {e}ᶜ,A j (x (p (j,false))) (x (p (j,true)))
  let b := d * ∏ j ∈ {incidenceIndex p q e}ᶜ,B j (x (q (j,false))) (x (q (j,true)))
  have extractA := product_extract_edge p A c e (x (p (e,false))) (x (p (e,true))) x
  have extractB := incidence_extract p q sameMatching B d e (x (p (e,false))) (x (p (e,true))) x
  rw [inserted] at extractA extractB
  have ha : a ≠ 0 := by
    intro zero
    apply hx
    rw [extractA]
    change A e (x (p (e,false))) (x (p (e,true))) * a = 0
    rw [zero,mul_zero]
  have hb : b ≠ 0 := by
    intro zero
    apply hx
    rw [same,extractB]
    change incidenceFactor p q B e (x (p (e,false))) (x (p (e,true))) * b = 0
    rw [zero,mul_zero]
  refine ⟨b/a,div_ne_zero hb ha,?_⟩
  funext u v
  have h := congrFun same (insertPair (p (e,false)) (p (e,true)) u v x)
  rw [product_extract_edge,incidence_extract p q sameMatching] at h
  change A e u v*a = incidenceFactor p q B e u v*b at h
  change A e u v = (b/a)*incidenceFactor p q B e u v
  field_simp [ha]
  linear_combination h

end Holant.LocalDrafts.RemoteWork.StableClosureV2.ClosureCompatibleAlignment
