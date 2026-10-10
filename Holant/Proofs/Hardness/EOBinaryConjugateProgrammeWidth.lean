import Holant.Proofs.Hardness.EOBinaryConjugateProgrammeBounds

/-! Bit-length bounds for every actual intermediate controller state. All root
and moment tapes are retained, and the unary round padding is charged as bytes. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeWidth
open Holant.OneHot Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open EOBinaryConjugateProgrammeState EOBinaryConjugateProgrammeBounds GraphPreprocessing
variable {L A : Type} [Field L] [Algebra ℚ L] [Fintype A] {d : ℕ}
variable (F : FixedField L d) (base : A→Fin d→ℚ)
variable (unit minus : A) (hunit : F.decode (base unit)=1) (hminus : F.decode (base minus) = -1)
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option Elab.async false

private theorem list_width {B : Type} (e : Computability.Encoding B Bool) (xs : List B) (W : ℕ)
    (h : ∀x∈xs,(e.encode x).length≤W) :
    ((framedListEncoding e).encode xs).length≤(2*W+2)*xs.length+1 := by
  induction xs with
  | nil => simp [framedListEncoding,framedListEncode]
  | cons x xs ih =>
    have hx:=h x (by simp)
    have ht:=ih (fun y hy=>h y (by simp [hy]))
    change (true::(frame (e.encode x)++framedListEncode e xs)).length≤_
    simp only [List.length_cons,List.length_append,frame_length]
    change (framedListEncode e xs).length≤_ at ht
    nlinarith

theorem encoding_length (s : State L) : ((encoding F).encode s).length=
    2*((rootsEncoding F).encode s.roots).length+2*((valuesEncoding F).encode s.moments).length+
    2*((rootsEncoding F).encode s.pending).length+2*((rootsEncoding F).encode s.remaining).length+
    2*((valuesEncoding F).encode s.values).length+2*(F.encoding.encode s.denominator).length+
    2*(F.encoding.encode s.multiplicity).length+2*(F.encoding.encode s.numerator).length+
    2*(F.encoding.encode s.divisor).length+s.fuel+9 := by
  simp only [encoding,fieldsEncoding,State.fields,pairEncoding_length,BinaryCSPProgrammeCore.unary,
    UnaryBinary.unaryEncoding,List.length_replicate]
  omega

theorem counts_le_bytes (s : State L) :
    s.roots.length≤((encoding F).encode s).length ∧
    s.moments.length≤((encoding F).encode s).length ∧
    s.fuel≤((encoding F).encode s).length := by
  have hr:=framedListEncoding_length_lower (scalarsEncoding F) s.roots
  have hm:=framedListEncoding_length_lower F.encoding s.moments
  rw [encoding_length]
  change 2*s.roots.length+1≤((rootsEncoding F).encode s.roots).length at hr
  change 2*s.moments.length+1≤((valuesEncoding F).encode s.moments).length at hm
  omega

include unit hunit in
theorem bounded_encoding {R U V B N : ℕ} {s : State L}
    (h : Bounded (fun a=>F.decode (base a)) R U V s)
    (hr : R≤B) (hu : U+filterBudget R s≤B) (hd : R+filterBudget R s≤B)
    (hc : scanned s+1≤B) (hv : V≤B)
    (hcounts : s.roots.length≤N ∧ s.moments.length≤N ∧ s.fuel≤N) :
    ((encoding F).encode s).length≤100*(ArithmeticSize.bitBound F base B+1)*(N+1) := by
  let W := ArithmeticSize.bitBound F base B
  have scalar {x : L} {b : ℕ} (hx : ArithmeticSize.Bound (fun a=>F.decode (base a)) b x)
      (hb : b≤B) : (F.encoding.encode x).length≤W :=
    (hx.mono unit hunit hb).encoded_length_le F base
  have pair {xs : List (L×L)}
      (hx : ∀p∈xs,ArithmeticSize.Bound (fun a=>F.decode (base a)) R p.1 ∧
        ArithmeticSize.Bound (fun a=>F.decode (base a)) R p.2) :
      ((rootsEncoding F).encode xs).length≤(6*W+4)*xs.length+1 := by
    have hw := list_width (scalarsEncoding F) xs (3*W+1) (fun p hp=>by
      rw [pairEncoding_length]
      have h₁:=scalar (hx p hp).1 hr
      have h₂:=scalar (hx p hp).2 hr
      omega)
    convert hw using 1 <;> ring
  have hrs := pair h.roots
  have hps := pair h.pending
  have hrem := pair h.remaining
  have hms := list_width F.encoding s.moments W (fun x hx=>scalar (h.moments x hx) (by omega))
  have hvs := list_width F.encoding s.values W (fun x hx=>scalar (h.values x hx) hu)
  have hden:=scalar h.denominator hd
  have hcnt:=scalar h.multiplicity hc
  have hnum:=scalar h.numerator hv
  have hdiv:=scalar h.divisor hv
  have hp:=h.pending_length.trans hcounts.1
  have hrr:=h.remaining_length.trans hcounts.1
  have hvv:=h.values_length.trans hcounts.2.1
  have h₁:=Nat.mul_le_mul_left (6*W+4) hcounts.1
  have h₂:=Nat.mul_le_mul_left (6*W+4) hp
  have h₃:=Nat.mul_le_mul_left (6*W+4) hrr
  have h₄:=Nat.mul_le_mul_left (2*W+2) hcounts.2.1
  have h₅:=Nat.mul_le_mul_left (2*W+2) hvv
  rw [encoding_length]
  change ((valuesEncoding F).encode s.moments).length≤_ at hms
  change ((valuesEncoding F).encode s.values).length≤_ at hvs
  change _≤100*(W+1)*(N+1)
  nlinarith

def budget (R U V N : ℕ) : ℕ :=
  R+U+V+(N+1)*(R+3)+N*(U+R+(N+1)*(R+3)+4)

include unit minus hunit hminus in
theorem iterate_encoding {R U V N : ℕ} {s : State L}
    (h : Bounded (fun a=>F.decode (base a)) R U V s)
    (hs : ((encoding F).encode s).length≤N) (i : ℕ) (hi : i≤N) :
    ((encoding F).encode ((step^[i]) s)).length≤
      100*(ArithmeticSize.bitBound F base (budget R U V N)+1)*(N+1) := by
  have hcounts:=counts_le_bytes F s
  have hroot:s.roots.length≤N:=hcounts.1.trans hs
  have hmom:s.moments.length≤N:=hcounts.2.1.trans hs
  have hfuel:s.fuel≤N:=hcounts.2.2.trans hs
  have hb:=bounded_iterate (fun a=>F.decode (base a)) unit minus hunit hminus h i
  have hscan:scanned ((step^[i]) s)≤N := by
    exact (Nat.sub_le _ _).trans (by simpa using hroot)
  have hfilter:filterBudget R ((step^[i]) s)≤N*(R+2):=Nat.mul_le_mul_right _ hscan
  have hterm:termBudget R U s≤U+R+(N+1)*(R+3)+4:=by
    unfold termBudget
    have hh:=Nat.mul_le_mul_right (R+3) (Nat.add_le_add_right hroot 1)
    omega
  have hacc:=Nat.mul_le_mul hi hterm
  apply bounded_encoding F base unit hunit hb
  · unfold budget; omega
  · unfold budget; nlinarith
  · unfold budget; nlinarith
  · unfold budget; nlinarith
  · unfold budget; omega
  · simpa only [iterate_roots,iterate_moments,iterate_fuel] using ⟨hroot,hmom,hfuel⟩

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryConjugateProgrammeWidth
