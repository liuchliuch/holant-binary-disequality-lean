import Holant.Certificates.EqualityQuaternary.MonomialSource

/-! Exact exotic representative-plane evaluation and its exceptional
endpoint dressing (A.7, 16065–16085). This is the representative-plane
proof clause; it does not assume or assert the unproved 24-plane atlas.
-/
noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Exotic
open Holant Holant.Marked Holant.Tractable Holant.Marked.SupportAtlas
open Holant.EightVertex.ProductAnchor (EndpointEven)

def E (k : Fin 4) : Mat :=
  if k=0 then Signature.equality else if k=1 then Signature.disequality
  else if k=2 then
    fun a b => if a then (if b then -imaginaryUnit else -1)
      else (if b then 1 else imaginaryUnit)
  else fun a b => if a then (if b then imaginaryUnit else -1)
      else (if b then 1 else -imaginaryUnit)

/-- Literal tensor sum of the four original exotic matrices. -/
def plane (a b : Scalar) : Signature Scalar 4 := fun w =>
  a*(E 0 (w 0) (w 1)*E 0 (w 2) (w 3) + E 1 (w 0) (w 1)*E 1 (w 2) (w 3)) +
  b*(E 2 (w 0) (w 1)*E 2 (w 2) (w 3) + E 3 (w 0) (w 1)*E 3 (w 2) (w 3))

theorem plane_table (a b : Scalar) (w : Word) :
    plane a b w = if parity w then 0 else if w 0=w 3 then a-2*b else a+2*b := by
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [plane,E,parity,h0,h1,h2,h3,Signature.equality,Signature.disequality]
  all_goals (ring_nf <;> norm_num [imaginaryUnit_sq] <;> ring)

theorem plane_complement (a b : Scalar) (w : Word) :
    plane a b (complement w)=plane a b w := by
  rw [plane_table,plane_table]
  cases h0 : w 0 <;> cases h1 : w 1 <;> cases h2 : w 2 <;> cases h3 : w 3 <;>
    simp [parity,complement,h0,h1,h2,h3]

def exceptionalMask : Word := ![false,false,true,true]

theorem exceptional_endpoints (b : Scalar) :
    Flip.value (plane (2*b) b) exceptionalMask (fun _ => false)=4*b ∧
      Flip.value (plane (2*b) b) exceptionalMask (fun _ => true)=4*b := by
  constructor <;> simp [Flip.value,plane_table,exceptionalMask,xorWord,parity,complement] <;> ring

/-- The source's exceptional a=2b endpoint-zero case keeps one original copy. -/
theorem representative_endpoint (a b : Scalar) (hq : plane a b≠0) :
    ∃ mask : Word, (mask=(fun _ => false) ∨ mask=exceptionalMask) ∧
      EndpointEven (Flip.value (plane a b) mask) := by
  by_cases he : a-2*b=0
  · have ha : a=2*b := sub_eq_zero.mp he
    have hb : b≠0 := by
      intro hb
      apply hq
      funext w
      simp [plane,ha,hb]
    refine ⟨exceptionalMask,Or.inr rfl,?_,?_,?_⟩
    · rw [ha,(exceptional_endpoints b).1]
      exact mul_ne_zero (by norm_num) hb
    · rw [ha,(exceptional_endpoints b).2]
      exact mul_ne_zero (by norm_num) hb
    · intro w hw
      change plane a b (xorWord w exceptionalMask)=0
      rw [plane_table,parity_xorWord,(parity_weight w).mpr hw]
      rfl
  · refine ⟨(fun _ => false),Or.inl rfl,?_,?_,?_⟩
    · simpa [Flip.value,xorWord,plane_table,parity,complement] using he
    · simpa [Flip.value,xorWord,plane_table,parity,complement] using he
    · intro w hw
      have hx : xorWord w (fun _ => false)=w := by funext i; simp [xorWord]
      rw [Flip.value,hx,plane_table,(parity_weight w).mpr hw]
      rfl

/-- Actual endpoint/nonmatching conclusion for the displayed exotic plane.
The safe-locus-to-plane reduction is deliberately not an input or a claim here. -/
theorem representative_boundary (F : SignatureFamily Scalar) (a b : Scalar)
    (hp : TensorPrime (plane a b))
    (hq : Gadget.Realizes F .disequality (plane a b))
    (hI : Gadget.Realizes F .disequality (kernelSignature Signature.equality)) :
    ∃ mask : Word, EndpointEven (Flip.value (plane a b) mask) ∧
      TensorPrime (Flip.value (plane a b) mask) ∧
      ¬GroupMatching {B | ∃ k c, c≠0 ∧ B=scale c (E k)} (Flip.value (plane a b) mask) ∧
      Gadget.Realizes F .disequality (Flip.value (plane a b) mask) ∧
      (Flip.network (plane a b) mask).denote=Flip.value (plane a b) mask ∧
      (Finset.univ.filter (fun v : Fin (Flip.network (plane a b) mask).shape.vertices =>
        (Flip.network (plane a b) mask).shape.arity v=4)).card=1 := by
  classical
  obtain ⟨mask,_,he⟩ := representative_endpoint a b hp.1
  have hp' := flip_prime hp mask
  exact ⟨mask,he,hp',prime_not_matching hp',Flip.actual F _ hq hI mask,
    Flip.denote _ mask,Flip.quaternary_count _ mask⟩

end Holant.Certificates.EqualityQuaternary.Exotic
